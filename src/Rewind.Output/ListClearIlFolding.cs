using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;

namespace Rewind.Output;

// Exact BCL Clear sequences. Value elements must be recursively
// reference-free. Reference elements require an exact, fresh Count snapshot
// on every path to the version read, plus the complete Array.Clear tail.
internal static partial class ListClearIlFolding
{
    private static string? Scope(TypeReference t)=>t.Scope switch
    {
        AssemblyNameReference a=>a.FullName,
        ModuleDefinition m=>m.Assembly?.Name.FullName,
        _=>null
    };
    private static bool Same(TypeReference a,TypeReference b)=>
        a.FullName==b.FullName && Scope(a) is {} s && s==Scope(b);
    private static bool Int(TypeReference t)=>t.MetadataType==MetadataType.Int32;
    private static bool Number(Instruction i,int n)=>i.OpCode.Code==Code.Ldc_I4&&i.Operand is int v&&v==n;
    private static bool Local(Instruction i,Code c,VariableDefinition v)=>i.OpCode.Code==c&&i.Operand==v;
    private static bool List(TypeReference t)=>t is GenericInstanceType g &&
        g.ElementType.FullName=="System.Collections.Generic.List`1" &&
        g.ElementType.Scope.Name is "mscorlib" or "System.Private.CoreLib" &&
        g.GenericArguments.Count==1&&!g.ContainsGenericParameter;
    private static bool ReferenceFree(TypeReference t,HashSet<TypeDefinition> visiting)
    {
        if(t is TypeSpecification or GenericParameter || t.ContainsGenericParameter)return false;
        if(t.MetadataType is MetadataType.Boolean or MetadataType.Char or MetadataType.SByte or MetadataType.Byte or
            MetadataType.Int16 or MetadataType.UInt16 or MetadataType.Int32 or MetadataType.UInt32 or MetadataType.Int64 or
            MetadataType.UInt64 or MetadataType.Single or MetadataType.Double or MetadataType.IntPtr or MetadataType.UIntPtr)
            return true;
        TypeDefinition? d;
        try{d=t.Resolve();}catch(AssemblyResolutionException){return false;}
        if(d==null||!d.IsValueType||d.HasGenericParameters||!visiting.Add(d))return false;
        bool safe=d.Fields.Where(f=>!f.IsStatic).All(f=>ReferenceFree(f.FieldType,visiting));
        visiting.Remove(d);return safe;
    }
    private static bool ManagedReference(TypeReference t)
    {
        if(t.IsValueType||t is ByReferenceType or PointerType or FunctionPointerType||t.ContainsGenericParameter)return false;
        if(t is ArrayType)return true;
        try{return t.Resolve() is {IsValueType:false};}
        catch(AssemblyResolutionException){return false;}
    }

    internal static int Run(MethodBody body)
    {
        if(!body.Instructions.Any(i=>i.OpCode.Code==Code.Ldfld && i.Operand is FieldReference f && f.Name=="_version"&&List(f.DeclaringType)))return 0;
        var original=body.Instructions.Select(i=>(i,i.OpCode,i.Operand)).ToArray();
        body.SimplifyMacros();int count=0;
        foreach(var i in body.Instructions.ToArray())
            if(i.OpCode.Code==Code.Ldfld&&i.Operand is FieldReference f&&f.Name=="_version"&&List(f.DeclaringType)&&TryFold(body,i))count++;
        if(count==0)foreach(var (i,opcode,operand) in original){i.OpCode=opcode;i.Operand=operand;}
        return count;
    }

    private static bool TryFold(MethodBody body,Instruction candidate)
    {
        var a=body.Instructions.ToArray();var ix=a.Select((i,n)=>(i,n)).ToDictionary(x=>x.i,x=>x.n);
        int k=ix[candidate]-1;
        if(k<0||k+11>=a.Length||a[k].OpCode.Code!=Code.Ldloc||
            a[k].Operand is not VariableDefinition list||list.VariableType is not GenericInstanceType gt||!List(gt)||
            a[k+2].OpCode.Code!=Code.Stloc||a[k+2].Operand is not VariableDefinition version||
            !Int(version.VariableType)||list==version)return false;
        TypeDefinition? def;
        try{def=gt.ElementType.Resolve();}catch(AssemblyResolutionException){return false;}
        if(def==null||!Same(def,gt.ElementType)||def.GenericParameters.Count!=1||
            Same(body.Method.DeclaringType,def))return false;
        bool Field(Instruction i,Code op,string name,bool items=false)
        {
            if(i.OpCode.Code!=op||i.Operand is not FieldReference f||f.Name!=name||!Same(f.DeclaringType,gt))return false;
            FieldDefinition? d;try{d=f.Resolve();}catch(AssemblyResolutionException){return false;}
            return d!=null&&d.DeclaringType==def&&!d.IsStatic&&(d.IsPrivate||d.IsAssembly)&&
                (items?d.FieldType is ArrayType{IsVector:true,ElementType:GenericParameter p}&&p.Position==0&&
                       p.Type==GenericParameterType.Type&&p.Owner is TypeReference owner&&Same(owner,gt.ElementType):Int(d.FieldType));
        }
        MethodDefinition? Resolve(MethodReference m){try{return m.Resolve();}catch(AssemblyResolutionException){return null;}}
        if(!Field(candidate,Code.Ldfld,"_version"))return false;
        int scheduled=0;
        // A read from this or a typed local, kept in its original position.
        // A Count null check precedes it, as the original version read did.
        if(k+14<a.Length&&a[k+3].OpCode.Code is Code.Ldarg or Code.Ldloc&&
            a[k+4].OpCode.Code==Code.Ldfld&&a[k+5].OpCode.Code==Code.Stloc)scheduled=3;
        if(scheduled==0&&ConditionalFieldStore(body,a,k+3,list,version))scheduled=11;
        int n=k+3+scheduled;
        if(n+8>=a.Length||!Local(a[n],Code.Ldloc,list)||!Number(a[n+1],0)||
            !Field(a[n+2],Code.Stfld,"_size")||!Local(a[n+3],Code.Ldloc,list)||
            !Local(a[n+4],Code.Ldloc,version)||!Number(a[n+5],1)||a[n+6].OpCode.Code!=Code.Add||
            !Field(a[n+7],Code.Stfld,"_version"))return false;
        var clears=def.Methods.Where(m=>m.Name=="Clear"&&m.IsPublic&&!m.IsStatic&&!m.HasGenericParameters&&
            m.Parameters.Count==0&&m.ReturnType.MetadataType==MetadataType.Void).ToArray();
        var counts=def.Methods.Where(m=>m.Name=="get_Count"&&m.IsPublic&&!m.IsStatic&&!m.HasGenericParameters&&
            m.Parameters.Count==0&&Int(m.ReturnType)).ToArray();
        if(clears.Length!=1||counts.Length!=1)return false;
        var clear=new MethodReference("Clear",clears[0].ReturnType,gt){HasThis=true,CallingConvention=clears[0].CallingConvention};
        var count=new MethodReference("get_Count",counts[0].ReturnType,gt){HasThis=true,CallingConvention=counts[0].CallingConvention};
        if(Resolve(clear)!=clears[0]||Resolve(count)!=counts[0])return false;
        var region=a.Skip(k).Take(n+8-k).ToHashSet();
        if(scheduled==3)
        {
            if(a[k+3].Operand==list||a[k+3].Operand==version||
                a[k+5].Operand is not VariableDefinition dst||dst==list||dst==version||
                a[k+4].Operand is not FieldReference rf||!Same(rf.FieldType,dst.VariableType))return false;
            TypeReference? source=a[k+3].Operand switch{ParameterDefinition p=>p.ParameterType,VariableDefinition v=>v.VariableType,_=>null};
            if(source==null||source.IsValueType||source is TypeSpecification||!Same(source,rf.DeclaringType))return false;
            FieldDefinition? rd;try{rd=rf.Resolve();}catch(AssemblyResolutionException){return false;}
            if(rd==null||rd.IsStatic||(!rd.IsPublic&&rd.DeclaringType!=body.Method.DeclaringType))return false;
        }
        bool refs=ManagedReference(gt.GenericArguments[0]);
        if(!refs&&!ReferenceFree(gt.GenericArguments[0],[]))return false;
        Instruction join=a[n+8];VariableDefinition? savedCount=null;
        int tail=n+8;
        bool leave=false;
        var countAliases=new HashSet<VariableDefinition>();
        var skippedBridge=new List<Instruction>();
        if(refs)
        {
            if(scheduled!=0||tail+12>=a.Length||a[tail].OpCode.Code!=Code.Ldloc||
                a[tail].Operand is not VariableDefinition cv||!Int(cv.VariableType)||cv==version||cv==list||
                !Number(a[tail+1],1)||a[tail+2].OpCode.Code!=Code.Clt||
                !FreshCountSnapshot(body,a,ix,k,list,gt,counts[0],cv,version,out countAliases))return false;
            savedCount=cv;
            int j;Instruction? exit=null;
            bool split=a[tail+3].OpCode.Code==Code.Brfalse;
            if(split)
            {
                if(a[tail+3].Operand is not Instruction nonempty||
                    a[tail+4].OpCode.Code is not (Code.Leave or Code.Br)||a[tail+4].Operand is not Instruction destination||
                    !ix.TryGetValue(nonempty,out j)||j!=tail+5)return false;
                exit=destination;leave=a[tail+4].OpCode.Code==Code.Leave;
            }
            else
            {
                if(a[tail+3].OpCode.Code!=Code.Brtrue||a[tail+3].Operand is not Instruction) return false;
                j=tail+4;
            }
            while(j<a.Length&&a[j].OpCode.Code==Code.Nop)j++;
            if(j+5>=a.Length||!Local(a[j],Code.Ldloc,list)||!Field(a[j+1],Code.Ldfld,"_items",true)||
                !Number(a[j+2],0)||!Local(a[j+3],Code.Ldloc,cv)||
                a[j+4].OpCode.Code!=Code.Call||a[j+4].Operand is not MethodReference ac||
                ac.DeclaringType.FullName!="System.Array"||Scope(ac.DeclaringType)!=Scope(gt)||
                ac.Name!="Clear"||ac.HasThis||ac.HasGenericParameters||ac is GenericInstanceMethod||ac.Parameters.Count!=3||
                ac.Parameters[0].ParameterType.FullName!="System.Array"||!Int(ac.Parameters[1].ParameterType)||
                !Int(ac.Parameters[2].ParameterType)||ac.ReturnType.MetadataType!=MetadataType.Void||
                Resolve(ac) is not {IsPublic:true,IsStatic:true})return false;
            if(split)
            {
                if(a[j+5].OpCode.Code!=a[tail+4].OpCode.Code||a[j+5].Operand!=exit)return false;
                join=exit!;
                foreach(var instruction in a.Skip(tail).Take(j+6-tail))region.Add(instruction);
            }
            else
            {
                join=a[j+5];Instruction skip=(Instruction)a[tail+3].Operand;
                if(skip!=join)
                {
                    if(!ix.TryGetValue(skip,out int bridge))return false;
                    int endBridge=bridge;
                    while(endBridge<a.Length&&endBridge-bridge<=4&&a[endBridge].OpCode.Code==Code.Nop)
                        skippedBridge.Add(a[endBridge++]);
                    if(endBridge>=a.Length||endBridge-bridge>4||a[endBridge].OpCode.Code!=Code.Br||a[endBridge].Operand!=join)return false;
                    skippedBridge.Add(a[endBridge]);
                }
                foreach(var instruction in a.Skip(tail).Take(j+5-tail))region.Add(instruction);
            }
        }
        // The count read stays in place. No external incoming edges into
        // the interior (including the version read after the Count snapshot).
        var entry=a[k];
        var allowed=region.ToHashSet();
        if(region.Contains(join))return false;
        foreach(var i in a)
        {
            if(i.OpCode.Code==Code.Ldloca&&(i.Operand==list||i.Operand==version||i.Operand==savedCount||i.Operand is VariableDefinition alias&&countAliases.Contains(alias)))return false;
            if(!region.Contains(i)&&i.Operand==version)return false;
            if(allowed.Contains(i))continue;
            if(i.Operand is Instruction t&&allowed.Contains(t)&&t!=entry)return false;
            if(i.Operand is Instruction[] ts&&ts.Any(t=>allowed.Contains(t)&&t!=entry))return false;
        }
        foreach(var h in body.ExceptionHandlers)
        {
            var boundaries=new[]{h.TryStart,h.TryEnd,h.HandlerStart,h.HandlerEnd,h.FilterStart};
            if(boundaries.Any(t=>t!=null&&allowed.Contains(t)&&t!=entry))return false;
            bool Inside(Instruction i,Instruction? start,Instruction? end)=>start!=null&&ix[i]>=ix[start]&&(end==null||ix[i]<ix[end]);
            int S(Instruction i)=>(Inside(i,h.TryStart,h.TryEnd)?1:0)|(Inside(i,h.HandlerStart,h.HandlerEnd)?2:0)|(Inside(i,h.FilterStart,h.HandlerStart)?4:0);
            int scope=S(entry);
            if((scope&4)!=0||allowed.Any(i=>S(i)!=scope)||skippedBridge.Any(i=>S(i)!=scope)||!leave&&S(join)!=scope)return false;
        }
        var preserve=scheduled==0?new HashSet<Instruction>():a.Skip(k+3).Take(scheduled).ToHashSet();
        foreach(var i in region)if(!preserve.Contains(i)){i.OpCode=OpCodes.Nop;i.Operand=null;}
        if(scheduled!=0)
        {
            a[k].OpCode=OpCodes.Ldloc;a[k].Operand=list;
            a[k+1].OpCode=OpCodes.Callvirt;a[k+1].Operand=count;
            a[k+2].OpCode=OpCodes.Pop;
        }
        a[n].OpCode=OpCodes.Ldloc;a[n].Operand=list;
        a[n+1].OpCode=OpCodes.Callvirt;a[n+1].Operand=clear;
        // Keep the final protected-region leave at the end of the original
        // region: unreachable NOPs must not fall through into a handler.
        if(leave){var exit=region.OrderBy(i=>ix[i]).Last();exit.OpCode=OpCodes.Leave;exit.Operand=join;}
        return true;
    }
}
