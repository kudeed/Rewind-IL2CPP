using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Rewind.Output;

/// <summary>
/// ECMA-335 representation for a recovered 64-bit integer snapshot read
/// as IEEE binary64. An overlapping primitive-only explicit-layout value
/// type preserves the bits without a mismatched managed-pointer ldobj or
/// a dependency on a CoreLib API that may have been stripped.
/// </summary>
internal sealed class DoubleBitCast
{
    internal const string HelperName = "__RewindDoubleBits";
    private readonly Dictionary<ModuleDefinition, (TypeDefinition Type, FieldDefinition Bits, FieldDefinition Value)> _layouts = [];

    internal int Run(Mono.Cecil.Cil.MethodBody body, TypeReference valueType)
    {
        var module=body.Method.Module;
        if (valueType.FullName!="System.ValueType" ||
            valueType.Scope.Name is not ("mscorlib" or "System.Private.CoreLib")) return 0;
        var instructions=body.Instructions.ToArray();
        var targets=new HashSet<Instruction>();
        foreach(var i in instructions)
        {
            if(i.Operand is Instruction dst)targets.Add(dst);
            if(i.Operand is Instruction[] dsts)foreach(var d in dsts)targets.Add(d);
        }
        foreach(var h in body.ExceptionHandlers)
            foreach(var b in new[]{h.TryStart,h.TryEnd,h.HandlerStart,h.HandlerEnd,h.FilterStart})
                if(b!=null)targets.Add(b);
        var sites=new List<(Instruction Address, Instruction Read, VariableDefinition Source)>();
        for(int i=0;i+1<instructions.Length;i++)
        {
            var address=instructions[i];var read=instructions[i+1];
            if(address.OpCode.Code is not (Code.Ldloca or Code.Ldloca_S) ||
                address.Operand is not VariableDefinition source ||
                source.VariableType.MetadataType is not (MetadataType.Int64 or MetadataType.UInt64) ||
                source.VariableType.Scope.Name!=valueType.Scope.Name ||
                read.OpCode.Code!=Code.Ldobj || read.Operand is not TypeReference t ||
                t.MetadataType!=MetadataType.Double || t.Scope.Name!=valueType.Scope.Name ||
                targets.Contains(read) || (i>0&&instructions[i-1].OpCode.OpCodeType==OpCodeType.Prefix)) continue;
            sites.Add((address,read,source));
        }
        if(sites.Count==0)return 0;
        if(!_layouts.TryGetValue(module,out var layout))
        {
            // Never adopt a same-named user type.
            if(module.Types.Any(t=>t.Namespace.Length==0&&t.Name==HelperName))return 0;
            var t=new TypeDefinition("",HelperName,
                TypeAttributes.NotPublic|TypeAttributes.Sealed|TypeAttributes.ExplicitLayout|TypeAttributes.BeforeFieldInit,
                module.ImportReference(valueType)){ClassSize=8,PackingSize=8};
            var bits=new FieldDefinition("Bits",FieldAttributes.Public,sites[0].Source.VariableType.MetadataType==MetadataType.Int64 ? sites[0].Source.VariableType : module.TypeSystem.Int64){Offset=0};
            var value=new FieldDefinition("Value",FieldAttributes.Public,(TypeReference)sites[0].Read.Operand){Offset=0};
            t.Fields.Add(bits);t.Fields.Add(value);module.Types.Add(t);
            layout=(t,bits,value);_layouts.Add(module,layout);
        }
        // A separate snapshot per method. All eight bytes are assigned
        // immediately before every read; no reference fields or aliases.
        var slot=new VariableDefinition(layout.Type);body.Variables.Add(slot);
        var il=body.GetILProcessor();
        foreach(var (address,read,source) in sites)
        {
            // Preserve existing entry and EH boundary at the first
            // instruction. No incoming branch is allowed at the old read.
            address.OpCode=OpCodes.Ldloca;address.Operand=slot;
            read.OpCode=OpCodes.Ldloc;read.Operand=source;
            var store=Instruction.Create(OpCodes.Stfld,layout.Bits);
            var load=Instruction.Create(OpCodes.Ldloca,slot);
            var value=Instruction.Create(OpCodes.Ldfld,layout.Value);
            il.InsertAfter(read,store);il.InsertAfter(store,load);il.InsertAfter(load,value);
        }
        return sites.Count;
    }
}
