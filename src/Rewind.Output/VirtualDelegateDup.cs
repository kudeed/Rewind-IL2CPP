using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;

namespace Rewind.Output;

/// <summary>Canonical CLI closed-instance virtual delegate construction.
/// Two identical stable reference loads already denote the same object.
/// Use dup for the second, retaining the original ldvirtftn, newobj and
/// all receiver/null/virtual dispatch semantics. Do not guess a target.</summary>
internal static class VirtualDelegateDup
{
    private static string? Scope(TypeReference t)=>t.Scope switch
    {
        AssemblyNameReference a=>a.FullName,
        ModuleDefinition m=>m.Assembly?.Name.FullName,
        _=>null
    };
    private static bool Same(TypeReference a,TypeReference b)=>
        a.FullName==b.FullName&&Scope(a) is {} x&&x==Scope(b);
    private static bool Core(TypeReference t,string name)=>
        t.FullName==name&&(t.Scope is ModuleDefinition m?m.Assembly?.Name.Name:t.Scope.Name) is "mscorlib" or "System.Private.CoreLib";
    private static TypeReference? LoadType(Instruction i)=>i.OpCode.Code switch
    {
        Code.Ldarg when i.Operand is ParameterDefinition p=>p.ParameterType,
        Code.Ldloc when i.Operand is VariableDefinition v=>v.VariableType,
        _=>null
    };
    private static bool Receiver(TypeReference source,TypeReference target)
    {
        if(source.IsValueType||source is TypeSpecification or GenericParameter||
           source.ContainsGenericParameter||target is TypeSpecification or GenericParameter||
           target.ContainsGenericParameter)return false;
        try
        {
            var t=source.Resolve();
            if(t==null||t.IsValueType)return false;
            var seen=new HashSet<TypeDefinition>();
            var pending=new Stack<TypeDefinition>();pending.Push(t);
            while(pending.TryPop(out var d))
            {
                if(!seen.Add(d))continue;
                if(Same(d,target))return true;
                if(d.BaseType is {} b && b is not TypeSpecification && b.Resolve() is {} parent)pending.Push(parent);
                foreach(var i in d.Interfaces)
                    if(i.InterfaceType is not TypeSpecification&&i.InterfaceType.Resolve() is {} iface)pending.Push(iface);
            }
        }
        catch(AssemblyResolutionException){}
        return false;
    }
    internal static int Run(MethodBody body)
    {
        if(!body.Instructions.Any(i=>i.OpCode.Code==Code.Ldvirtftn))return 0;
        var original=body.Instructions.Select(i=>(i,i.OpCode,i.Operand)).ToArray();
        body.SimplifyMacros();
        var targets=new HashSet<Instruction>();
        foreach(var i in body.Instructions)
        {
            if(i.Operand is Instruction dst)targets.Add(dst);
            if(i.Operand is Instruction[] ds)foreach(var d in ds)targets.Add(d);
        }
        foreach(var h in body.ExceptionHandlers)
            foreach(var i in new[]{h.TryStart,h.TryEnd,h.HandlerStart,h.HandlerEnd,h.FilterStart})
                if(i!=null)targets.Add(i);
        int folded=0;var a=body.Instructions.ToArray();
        for(int n=0;n+3<a.Length;n++)
        {
            var first=a[n];var second=a[n+1];var ptr=a[n+2];var ctor=a[n+3];
            if(LoadType(first) is not {} source||first.OpCode.Code!=second.OpCode.Code||
               first.Operand!=second.Operand||targets.Contains(second)||targets.Contains(ptr)||targets.Contains(ctor)||
               (n>0&&a[n-1].OpCode.OpCodeType==OpCodeType.Prefix)||
               ptr.OpCode.Code!=Code.Ldvirtftn||ptr.Operand is not MethodReference callee||
               !callee.HasThis||callee.Name is ".ctor" or ".cctor"||callee is GenericInstanceMethod||
               !Receiver(source,callee.DeclaringType)||
               ctor.OpCode.Code!=Code.Newobj||ctor.Operand is not MethodReference c||
               c.Name!=".ctor"||!c.HasThis||c.Parameters.Count!=2||
               !Core(c.Parameters[0].ParameterType,"System.Object")||!Core(c.Parameters[1].ParameterType,"System.IntPtr")||
               c.ReturnType.MetadataType!=MetadataType.Void)continue;
            MethodDefinition? d,m;
            try{d=c.Resolve();m=callee.Resolve();}catch(AssemblyResolutionException){continue;}
            if(d==null||m==null||!d.IsConstructor||d.IsStatic||m.IsStatic||
               d.DeclaringType.BaseType is not {} parent||!Core(parent,"System.MulticastDelegate"))continue;
            // No signature adaptation is being made; even a previously
            // invalid target signature remains subject to ILVerify.
            second.OpCode=OpCodes.Dup;second.Operand=null;folded++;
        }
        if(folded==0)foreach(var (i,op,operand) in original){i.OpCode=op;i.Operand=operand;}
        return folded;
    }
}
