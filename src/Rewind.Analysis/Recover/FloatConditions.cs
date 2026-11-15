using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Comparing two floating point numbers has four possible outcomes: less, equal, greater, or unordered (one of
/// them is NaN). The CPU reports the outcome through several flags, so compiled code often tests one comparison
/// with two branches or a combination of flag conditions. Every such combination is just a set of outcomes, and
/// every set has one canonical way of writing it. Reducing conditions to their outcome set and writing the set
/// back out turns "unordered, or not (equal or unordered)" into "not equal".
/// </summary>
internal static class FloatConditions
{
    public const int Less = 1, Equal = 2, Greater = 4, Unordered = 8, All = 15;

    /// <summary>
    /// Describes <paramref name="condition"/> as the set of outcomes of comparing <paramref name="a"/> with
    /// <paramref name="b"/> for which it holds. The operand pair is taken from the first comparison found;
    /// fails when the condition involves anything else.
    /// </summary>
    public static bool TryMask(Node condition, ref Node? a, ref Node? b, out int mask, int depth = 0)
    {
        mask = 0;
        if (depth > 8 || condition.Type != VT.I1) return false;
        switch (condition.Op)
        {
            case Op.Const:
                mask = condition.Imm != 0 ? All : 0;
                return true;
            case Op.FCmpEq or Op.FCmpLt or Op.FCmpLe or Op.FCmpUnord:
            {
                Node x = condition.In[0], y = condition.In[1];
                bool swapped;
                if (a == null || b == null)
                {
                    a = x;
                    b = y;
                    swapped = false;
                }
                else if (Normalizer.SameValue(x, a) && Normalizer.SameValue(y, b)) swapped = false;
                else if (Normalizer.SameValue(x, b) && Normalizer.SameValue(y, a)) swapped = true;
                else return false;
                mask = condition.Op switch
                {
                    Op.FCmpEq => Equal,
                    Op.FCmpLt => swapped ? Greater : Less,
                    Op.FCmpLe => (swapped ? Greater : Less) | Equal,
                    _ => Unordered,
                };
                return true;
            }
            case Op.And or Op.Or or Op.Xor:
            {
                if (!TryMask(condition.In[0], ref a, ref b, out int left, depth + 1)) return false;
                if (!TryMask(condition.In[1], ref a, ref b, out int right, depth + 1)) return false;
                mask = condition.Op switch { Op.And => left & right, Op.Or => left | right, _ => left ^ right };
                return true;
            }
            default:
                return false;
        }
    }

    /// <summary>True when the condition is already a single comparison or the negation of one.</summary>
    public static bool IsSimple(Node condition)
    {
        if (condition.Op == Op.Xor && condition.In[1].IsConstValue(1)) condition = condition.In[0];
        return condition.Op is Op.FCmpEq or Op.FCmpLt or Op.FCmpLe or Op.FCmpUnord or Op.Const;
    }

    private static Node? Direct(IrBuilder ir, int mask, Node a, Node b) => mask switch
    {
        Equal => ir.Raw(Op.FCmpEq, VT.I1, a, b),
        Less => ir.Raw(Op.FCmpLt, VT.I1, a, b),
        Greater => ir.Raw(Op.FCmpLt, VT.I1, b, a),
        Less | Equal => ir.Raw(Op.FCmpLe, VT.I1, a, b),
        Greater | Equal => ir.Raw(Op.FCmpLe, VT.I1, b, a),
        Unordered => ir.Raw(Op.FCmpUnord, VT.I1, a, b),
        _ => null,
    };

    /// <summary>Writes an outcome set as the shortest condition that is true for exactly those outcomes.</summary>
    public static Node Canonical(IrBuilder ir, int mask, Node a, Node b)
    {
        // A value compared with itself can only be equal or unordered.
        int possible = Normalizer.SameValue(a, b) ? Equal | Unordered : All;
        mask &= possible;
        if (mask == 0) return ir.Const(VT.I1, 0);
        if (mask == possible) return ir.Const(VT.I1, 1);
        if (Direct(ir, mask, a, b) is { } direct) return direct;
        if (Direct(ir, possible & ~mask, a, b) is { } inverse) return ir.NotBool(inverse);
        // "Ordered and different" and its complement need two comparisons.
        Node different = ir.Or(ir.Raw(Op.FCmpLt, VT.I1, a, b), ir.Raw(Op.FCmpLt, VT.I1, b, a));
        return mask == (Less | Greater) ? different : ir.NotBool(different);
    }
}
