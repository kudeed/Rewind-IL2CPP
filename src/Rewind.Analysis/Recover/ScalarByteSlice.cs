using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Reads a register slice from a small struct whose requested bytes each have a public byte field.
/// The native loaders supported by this pass are little-endian. Every byte must be covered exactly;
/// padding, references, floating point fields, unknown layout and effects in the owner are rejected.
/// </summary>
internal static class ScalarByteSlice
{
    private static int IntegralBytes(TypeSig type) => type is PrimitiveSig p ? p.Element switch
    {
        Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.Boolean => 1,
        Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.Char => 2,
        Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 => 4,
        Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 => 8,
        _ => 0,
    } : 0;

    internal static HExpr? Read(HExpr value, TypeLayout layout, int offset, int size, SigFactory sigs)
    {
        // A full-width read is still the managed struct. Packing it early would force otherwise-typed
        // struct phi inputs to merge with integers. Only a proper subrange is a scalar slice.
        if (value is not HLocal local || local.Variable.AddressTaken ||
            local.Variable.Type is not { Definition: { IsValueType: true, IsEnum: false } definition } type ||
            type is ByRefSig or PointerSig || type.ContainsGenericParameter ||
            value.Type != null && value.Type.Key != type.Key || !layout.Known ||
            layout.Size is < 2 or > 8 || size is not (2 or 4) || size >= layout.Size ||
            offset < 0 || offset > layout.Size - size) return null;
        if (layout.Fields.Any(slot => slot.Size <= 0 || slot.Offset < 0 || slot.Offset > layout.Size - slot.Size ||
            slot.Field.IsStatic || !ReferenceEquals(slot.Field.DeclaringType, definition) ||
            slot.Field.Type.Key != slot.Type.Key)) return null;
        // A union's wider integer overlay is harmless; managed references and non-integral representations
        // must never be rebuilt by treating arbitrary managed storage as integer bits.
        foreach (FieldSlot slot in layout.Fields)
            if (slot.Offset < offset + size && offset < slot.Offset + slot.Size &&
                (IntegralBytes(slot.Type) != slot.Size)) return null;
        var bytes = new FieldSlot[size];
        for (int i = 0; i < size; i++)
        {
            var candidates = layout.Fields.Where(slot => slot.Offset == offset + i && slot.Size == 1 &&
                slot.Type is PrimitiveSig { Element: Il2CppTypeEnum.U1 } && !slot.Field.IsStatic &&
                (slot.Field.Attrs & FieldDef.AccessMask) == 6 && ReferenceEquals(slot.Field.DeclaringType, definition) &&
                slot.Field.Type.Key == slot.Type.Key).ToArray();
            if (candidates.Length != 1) return null;
            bytes[i] = candidates[0];
        }
        if (bytes.Select(slot => slot.Field).Distinct().Count() != size) return null;
        TypeSig u32 = sigs.Primitive(Il2CppTypeEnum.U4), i32 = sigs.Primitive(Il2CppTypeEnum.I4);
        HExpr? combined = null;
        for (int i = 0; i < size; i++)
        {
            FieldSlot slot = bytes[i];
            HExpr part = new HConv(HConvKind.U4, new HField
            {
                Object = new HLocal(local.Variable) { Type = type }, Field = slot.Field,
                DeclaringType = type, Type = slot.Type,
            }) { Type = u32 };
            if (i != 0) part = new HBinary(HBinaryOp.Shl, part, new HConst(i * 8, i32)) { Type = u32 };
            combined = combined == null ? part : new HBinary(HBinaryOp.Or, combined, part) { Type = u32 };
        }
        return size == 2 ? new HConv(HConvKind.U2, combined!) { Type = sigs.Primitive(Il2CppTypeEnum.U2) } : combined;
    }
}
