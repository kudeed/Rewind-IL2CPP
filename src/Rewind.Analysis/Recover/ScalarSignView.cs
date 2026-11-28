using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// The sign of a complete little-endian struct register is the sign of the signed integral field
/// ending at that register's top byte. This recognizes only a signed less-than-zero observation,
/// not a conversion of the struct to a number or an ordering of arbitrary aggregate values.
/// </summary>
internal static class ScalarSignView
{
    private static int IntegralBytes(TypeSig type) => type is PrimitiveSig p ? p.Element switch
    {
        Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 => 1,
        Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 => 2,
        Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 => 4,
        Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 => 8,
        _ => 0,
    } : 0;

    internal static HExpr? Compare(Op op, VT register, Node zero, HExpr value, TypeLayout layout, SigFactory sigs)
    {
        if (op != Op.CmpLtS || register is not (VT.I32 or VT.I64) ||
            zero.Dead || zero.Op != Op.Const || zero.Type != register || zero.Imm != 0 ||
            zero.Aux != null || zero.In.Length != 0 || value is not HLocal local || local.Variable.AddressTaken ||
            local.Variable.Type is not TypeDefSig { Definition: { IsValueType: true, IsEnum: false } definition } type ||
            type.ContainsGenericParameter || value.Type != null && value.Type.Key != type.Key ||
            !layout.Known || layout.Size != register.Bytes() || layout.DataSize != layout.Size ||
            layout.Fields.Length < 2) return null;
        // Validate every interval before adding offsets, including malformed/overflowing layouts.
        // Overlays are rejected so a top field cannot conceal a different native representation.
        foreach (FieldSlot slot in layout.Fields)
            if (slot.Size <= 0 || slot.Size > layout.Size || slot.Offset < 0 || slot.Offset > layout.Size - slot.Size ||
                slot.Field.IsStatic || !ReferenceEquals(slot.Field.DeclaringType, definition) ||
                slot.Field.Type.Key != slot.Type.Key || IntegralBytes(slot.Type) != slot.Size) return null;
        for (int i = 0; i < layout.Fields.Length; i++)
            for (int j = i + 1; j < layout.Fields.Length; j++)
                if (layout.Fields[i].Offset < layout.Fields[j].Offset + layout.Fields[j].Size &&
                    layout.Fields[j].Offset < layout.Fields[i].Offset + layout.Fields[i].Size) return null;
        FieldSlot[] tops = layout.Fields.Where(slot => slot.Offset + slot.Size == layout.Size &&
            slot.Type is PrimitiveSig { Element: Il2CppTypeEnum.I1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.I8 } &&
            (slot.Field.Attrs & FieldDef.AccessMask) == 6).ToArray();
        if (tops.Length != 1) return null;
        FieldSlot top = tops[0];
        var field = new HField
        {
            Object = new HLocal(local.Variable) { Type = type }, Field = top.Field,
            DeclaringType = type, Type = top.Type,
        };
        return new HCompare(HCompareOp.Lt, field, new HConst(0, top.Type))
        {
            Type = sigs.Primitive(Il2CppTypeEnum.Boolean),
        };
    }
}
