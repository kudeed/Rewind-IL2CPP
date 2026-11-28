using Rewind.Analysis.Hir;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>Restore the declared result type of an accessor that replaced a
/// direct native field read. Narrow it only with exact field/getter evidence.</summary>
internal static class WiderGetterResult
{
    private static bool PlainRef(TypeSig? sig) =>
        sig is TypeDefSig { Definition: { IsValueType:false, IsGenericDefinition:false } };

    private static bool Assignable(TypeDef from, TypeDef to)
    {
        var seen=new HashSet<TypeDef>();
        var pending=new Stack<TypeDef>();
        pending.Push(from);
        while(pending.TryPop(out var t))
        {
            if(!seen.Add(t))continue;
            if(ReferenceEquals(t,to))return true;
            if(t.BaseType is TypeDefSig b && PlainRef(b))pending.Push(b.Definition);
            foreach(var i in t.Interfaces)
                if(i is TypeDefSig d && PlainRef(d))pending.Push(d.Definition);
        }
        return false;
    }

    internal static bool ProvesFieldReturn(MethodDef getter,FieldDef field,TypeSig? expected,
        uint first,uint second,int extent,bool arm64,int pointerSize)
    {
        if(!arm64||pointerSize!=8||extent!=8||getter.IsStatic||getter.IsVirtual||getter.IsAbstract||
           getter.IsConstructor||getter.IsGenericDefinition||getter.Parameters.Length!=0||
           getter.DeclaringType.IsValueType||getter.DeclaringType.IsGenericDefinition||
           field.IsStatic||!ReferenceEquals(getter.DeclaringType,field.DeclaringType)||
           !PlainRef(field.Type)||!PlainRef(expected)||!PlainRef(getter.ReturnType)||
           !ReferenceEquals(expected,field.Type)||ReferenceEquals(field.Type,getter.ReturnType)||
           field.Offset<16||field.Offset%8!=0||field.Offset/8>4095||
           getter.DeclaringType.Fields.Count(f=>!f.IsStatic&&f.Offset==field.Offset)!=1||
           !getter.DeclaringType.Fields.Contains(field))return false;
        if(!Assignable(field.Type.Definition!,getter.ReturnType.Definition!)||
           Assignable(getter.ReturnType.Definition!,field.Type.Definition!))return false;
        return first==(0xf9400000u|((uint)(field.Offset/8)<<10)) && second==0xd65f03c0u;
    }

    internal static HExpr? TryRestore(HField field,HCall call,ProgramAnalysis program)
    {
        var getter=call.Method;var image=program.Model.Image;
        if(Environment.GetEnvironmentVariable("REWIND_NO_TYPED_WIDER_GETTER")!=null||
           call.This==null||call.Virtual||call.Constrained!=null||call.Arguments.Length!=0||
           call.MethodArguments.Length!=0||call.DeclaringType!=null||
           !ReferenceEquals(call.This.Type?.Definition,getter.DeclaringType)||
           getter.Address==0||program.RangeOf(getter.Address) is not {} r||
           r.Start!=getter.Address||r.End-r.Start!=8||!image.IsCodeAddress(r.Start)||
           !image.IsMapped(r.Start,8))return null;
        if(!ProvesFieldReturn(getter,field.Field,field.Type,image.U32(r.Start),
              image.U32(r.Start+4),8,image.Arch==CpuArch.Arm64,image.PointerSize))return null;
        call.Type=getter.ReturnType;
        return new HTypeExpr(HTypeOp.CastClass,field.Field.Type,call){Type=field.Field.Type};
    }
}
