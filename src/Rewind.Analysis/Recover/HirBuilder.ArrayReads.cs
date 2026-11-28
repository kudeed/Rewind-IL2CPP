using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    /// <summary>
    /// A native scalar-width read over several complete primitive array elements. The resolved element
    /// proves alignment and the element scale; its type proves how many bytes each entry contributes.
    /// Keep those entries separate so taking the high half reads the next entry, not bits above the first.
    /// </summary>
    private Sem WideArrayRead(Node load, HElement first, TypeSig elementType, int elementSize)
    {
        int size = load.Type.Bytes();
        string? why = null;
        if (first.Array.Type is not SzArraySig array || array.ElementType.Key != elementType.Key ||
            first.Type?.Key != elementType.Key)
            why = "wide array read has no exact element type";
        else if (elementType is not PrimitiveSig
                 { Element: Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or
                     Il2CppTypeEnum.Char or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.R4 } ||
                 elementSize is not (1 or 2 or 4) || size is not (2 or 4 or 8) || size <= elementSize || size % elementSize != 0)
            why = "wide array read is not a complete primitive range";
        // The existing materializer reads every part at the load before later calls/stores. Without that
        // planned snapshot a consumer might retain only one lane and silently drop the other array reads.
        else if (!_materialize.Contains(load))
            why = "wide array read has no planned complete snapshot";
        else if (!RepeatableArrayOperand(first.Array) || !RepeatableArrayOperand(first.Index) ||
                 first.Index.Type is not PrimitiveSig { Element: Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 })
            why = "wide array read would repeat an unproved address computation";
        if (why != null)
        {
            Problem(why);
            return new SVal(Site(new HOpaque("wide_array_read", first.Array, first.Index)
                { Type = TypeForBits(load.Type) }, why));
        }

        var parts = new List<Part>(size / elementSize);
        for (int offset = 0; offset < size; offset += elementSize)
        {
            int next = offset / elementSize;
            // HBinary.Add emits ordinary unchecked integer addition. Keep index+1 in the array access;
            // no clamp, mask, fallback or swallowed null/bounds exception is introduced.
            HExpr index = next == 0 ? first.Index
                : new HBinary(HBinaryOp.Add, first.Index, new HConst(next, _int)) { Type = _int };
            parts.Add(new Part(offset, elementSize,
                new HElement { Array = first.Array, Index = index, Type = elementType }));
        }
        return new SParts(parts, size);
    }

    /// <summary>
    /// Address components whose repeated evaluation between consecutive primitive reads has no call,
    /// indirect/array read, checked arithmetic, or conversion that could change state. Only immutable
    /// fields are repeated: a mutable/volatile field is not a captured native address, even when this
    /// thread performs no intervening store. A readonly field path can fail before the first read.
    /// </summary>
    private static bool RepeatableArrayOperand(HExpr e) => e switch
    {
        HArg or HLocal or HConst => true,
        HField field => (field.Field.Attrs & (FieldDef.InitOnly | FieldDef.Literal)) != 0 &&
            (field.Object == null || RepeatableArrayOperand(field.Object)),
        HUnary unary => RepeatableArrayOperand(unary.Operand),
        HBinary binary => (binary.Op is HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.Mul or HBinaryOp.And or
            HBinaryOp.Or or HBinaryOp.Xor or HBinaryOp.Shl or HBinaryOp.Shr or HBinaryOp.ShrUn) &&
            RepeatableArrayOperand(binary.Left) && RepeatableArrayOperand(binary.Right),
        HConv conv => conv.Kind < HConvKind.OvfI1 && RepeatableArrayOperand(conv.Operand),
        _ => false,
    };
}
