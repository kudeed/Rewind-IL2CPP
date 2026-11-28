using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Output;

/// <summary>
/// Recognize the explicit low/high 32-bit float reconstruction of an already
/// typed 8-byte struct snapshot. This is not a general struct-to-int cast.
/// Only complete sequential public two-float layouts qualify; preserve
/// the exact local, bit lane, and result type. All other aggregate numeric
/// operations still reach the existing fail-closed guard.
/// </summary>
internal static class PackedFloatLane
{
    internal static HField? Resolve(HCall call, bool littleEndianArm64, int header)
    {
        if (!littleEndianArm64 || header != 16 ||
            call is not { This: null, Virtual: false, Constrained: null, MethodArguments.Length: 0,
                Arguments: [HConv { Kind: HConvKind.I4, Type: PrimitiveSig { Element: Il2CppTypeEnum.I4 } } conv],
                Type: PrimitiveSig { Element: Il2CppTypeEnum.R4 } }) return null;
        var m=call.Method;
        if (m.DeclaringType.ReflectionName!="System.BitConverter" ||
            m.DeclaringType.Assembly.Name is not ("mscorlib" or "System.Private.CoreLib") ||
            m.Name!="Int32BitsToSingle" || !m.IsStatic || m.IsVirtual ||
            (m.Flags&MethodDef.AccessMask)!=6 || m.GenericParameters.Length!=0 ||
            m.ReturnType is not PrimitiveSig { Element: Il2CppTypeEnum.R4 } ||
            m.Parameters is not [{ Type: PrimitiveSig { Element: Il2CppTypeEnum.I4 } }]) return null;
        var bits=conv.Operand;
        int offset=0;
        if (bits is HBinary { Op: HBinaryOp.ShrUn, Right: HConst { Value: 32, Type: PrimitiveSig { Element: Il2CppTypeEnum.I4 } },
            Type: PrimitiveSig { Element: Il2CppTypeEnum.U8 or Il2CppTypeEnum.I8 } } shifted)
        {
            offset=4;
            bits=shifted.Left;
        }
        if (bits is not HLocal local ||
            local.Variable.Type is not TypeDefSig actual ||
            local.Type is not TypeDefSig annotation ||
            !ReferenceEquals(annotation.Definition,actual.Definition)) return null;
        var t=actual.Definition;
        if (!t.IsValueType || t.IsEnum || t.IsByRefLike || t.GenericParameters.Length!=0 ||
            (t.Flags&TypeDef.LayoutMask)!=TypeDef.SequentialLayout ||
            t.Sizes.InstanceSize!=header+8 || t.Sizes.NativeSize!=8) return null;
        var fields=t.Fields.Where(f=>!f.IsStatic).OrderBy(f=>f.Offset).ToArray();
        if (fields.Length!=2) return null;
        for(int i=0;i<2;i++)
        {
            var f=fields[i];
            if (!ReferenceEquals(f.DeclaringType,t) || f.Offset!=header+4*i ||
                (f.Attrs&FieldDef.AccessMask)!=6 ||
                f.Type is not PrimitiveSig { Element: Il2CppTypeEnum.R4 }) return null;
        }
        var lane=fields[offset/4];
        return new HField { Object=local, Field=lane, DeclaringType=actual, Type=lane.Type };
    }
}
