using Rewind.Analysis.Hir;
using Rewind.Analysis.Runtime;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

// Put a public getter back when the compiler has inlined an otherwise
// inaccessible reference-field dereference and a scalar property getter.
internal static class Arm64ChainedGetter
{
    internal static bool Matches(uint[] code,int first,int second,ulong address,Func<ulong,bool> nullThrow)
    {
        if(code.Length!=6||first<0||first%8!=0||first/8>4095||second<0||second%4!=0||second/4>4095)return false;
        uint reg=code[0]&31;
        if(reg==0||reg==31)return false;
        if(code[0]!=(0xf9400000u|((uint)(first/8)<<10)|reg)||
           code[1]!=(0xb4000000u|(3u<<5)|reg)||
           code[2]!=(0xb9400000u|((uint)(second/4)<<10)|(reg<<5))||
           code[3]!=0xd65f03c0u||code[4]!=0xf81f0ffeu||(code[5]&0xfc000000u)!=0x94000000u)return false;
        long delta=((long)(int)(code[5]<<6)>>6)*4;
        return nullThrow(unchecked((ulong)((long)address+20+delta)));
    }

    internal static HCall? TryFold(HField outer,MethodDef current,ProgramAnalysis program)
    {
        if(outer.Object is not HField field||outer.Field.IsStatic||
            !ReferenceEquals(outer.Field.DeclaringType,field.Field.Type.Definition))return null;
        return Fold(field,outer.Field.Offset,outer.Field.Type,outer.Type,current,program);
    }

    internal static HCall? TryFold(HCall call,MethodDef current,ProgramAnalysis program)
    {
        if(call is not {This:HField field,Arguments.Length:0,MethodArguments.Length:0,Virtual:false}||
           call.Method.IsStatic||call.Method.IsVirtual||call.Method.IsAbstract||call.Method.IsGenericDefinition||
           !ReferenceEquals(call.Method.DeclaringType,field.Field.Type.Definition)||
           program.Model.Image.Arch!=CpuArch.Arm64||
           program.RangeOf(call.Method.Address) is not {} shortRange||shortRange.End-shortRange.Start!=8)
            return null;
        uint w=program.Model.Image.U32(shortRange.Start);
        if((w&0xffc003ffu)!=0xb9400000u||program.Model.Image.U32(shortRange.Start+4)!=0xd65f03c0u)return null;
        return Fold(field,(int)((w>>10)&4095)*4,call.Method.ReturnType,call.Type,current,program);
    }

    private static HCall? Fold(HField field,int offset,TypeSig ret,TypeSig? result,MethodDef current,ProgramAnalysis program)
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_CHAINED_GETTER")!=null||
           program.Model.Image.Arch!=CpuArch.Arm64||field.Object is not {} receiver||
           field.Field.IsStatic||AccessorFolding.IsAccessible(field.Field,current)||
           field.Field.Type is not TypeDefSig inner||inner.Definition.IsValueType||inner.Definition.IsGenericDefinition||
           (receiver.Type??(receiver as HLocal)?.Variable.Type) is not TypeDefSig outer||
           !ReferenceEquals(outer.Definition,field.Field.DeclaringType)||outer.Definition.IsValueType||outer.Definition.IsGenericDefinition)
           return null;
        if((ret.Definition?.EnumUnderlyingType??ret) is not PrimitiveSig {Element:Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4})return null;
        if(inner.Definition.Fields.Count(f=>!f.IsStatic&&f.Offset==offset&&f.Type.Key==ret.Key)!=1)return null;
        var image=program.Model.Image;
        var matches=outer.Definition.Properties.Select(p=>p.Getter).OfType<MethodDef>().Where(m=>
            m!=current&&!m.IsStatic&&!m.IsVirtual&&!m.IsAbstract&&!m.IsGenericDefinition&&m.Parameters.Length==0&&
            (m.Flags&MethodDef.AccessMask)==6&&m.ReturnType.Key==ret.Key&&
            program.RangeOf(m.Address) is {} r&&r.End-r.Start==24&&
            Matches(Enumerable.Range(0,6).Select(i=>image.U32(r.Start+(ulong)i*4)).ToArray(),
                field.Field.Offset,offset,r.Start,a=>program.Helpers.KindAt(a)==HelperKind.ThrowNullReference)).Distinct().ToArray();
        if(matches.Length!=1)return null;
        return new HCall{Method=matches[0],This=receiver,Arguments=[],Type=result??ret};
    }
}
