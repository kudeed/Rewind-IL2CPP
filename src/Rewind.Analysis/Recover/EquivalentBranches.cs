using Rewind.Analysis.Hir;

namespace Rewind.Analysis.Recover;

/// <summary>
/// A condition with no observable evaluation is unnecessary when both successors do exactly the same work.
/// This includes metadata-initialization diamonds after their class/context phi has retained its identity.
/// No call, memory read, checked arithmetic, exception edge, or differing assignment can be discarded.
/// </summary>
internal static class EquivalentBranches
{
    internal static bool TryTarget(HMethod method, HBlock source, out HBlock? target)
    {
        target = null;
        if (method.TryRegions.Count != 0 || source.Scope != -1 || source.Statements.LastOrDefault() is not HBranch branch || !Inert(branch.Condition)) return false;
        var blocks = new HashSet<HBlock>(method.Blocks);
        HBlock? Trim(HBlock block)
        {
            var seen = new HashSet<HBlock>();
            for (int count = 0; count < 64; count++)
            {
                if (!blocks.Contains(block) || block.Scope != source.Scope || ReferenceEquals(block, source) || !seen.Add(block)) return null;
                if (block.Statements is not [HJump jump]) return block;
                block = jump.Target;
            }
            return null;
        }
        HBlock? yes = Trim(branch.WhenTrue), no = Trim(branch.WhenFalse);
        if (yes == null || no == null) return false;
        if (ReferenceEquals(yes, no)) { target = yes; return true; }
        if (yes.Statements.Count is < 2 or > 9 || yes.Statements.Count != no.Statements.Count ||
            yes.Statements[^1] is not HJump yesJump || no.Statements[^1] is not HJump noJump) return false;
        HBlock? yesNext = Trim(yesJump.Target), noNext = Trim(noJump.Target);
        if (yesNext == null || !ReferenceEquals(yesNext, noNext)) return false;
        for (int i = 0; i < yes.Statements.Count - 1; i++)
            if (yes.Statements[i] is not HAssign { Target: HLocal a, Value: var av } ||
                no.Statements[i] is not HAssign { Target: HLocal b, Value: var bv } ||
                !ReferenceEquals(a.Variable, b.Variable) || !SameCopy(av, bv)) return false;
        target = yes; // retain one complete copy of the identical assignments
        return true;
    }

    private static bool SameCopy(HExpr a, HExpr b)
    {
        if (a.Type?.Key != b.Type?.Key) return false;
        return (a, b) switch
        {
            (HLocal x, HLocal y) => ReferenceEquals(x.Variable, y.Variable),
            (HArg x, HArg y) => x.Index == y.Index,
            (HConst { Value: float x }, HConst { Value: float y }) => BitConverter.SingleToInt32Bits(x) == BitConverter.SingleToInt32Bits(y),
            (HConst { Value: double x }, HConst { Value: double y }) => BitConverter.DoubleToInt64Bits(x) == BitConverter.DoubleToInt64Bits(y),
            (HConst x, HConst y) => Equals(x.Value, y.Value),
            _ => false,
        };
    }

    private static bool Inert(HExpr value) => value switch
    {
        HConst or HLocal or HArg => true,
        // These are values of already-described machine registers/metadata, not unknown native operations.
        // Their actual value is irrelevant only after both successor computations are proved identical.
        HOpaque { Text: "undefined" or "klass" or "rgctx", Operands.Length: 0 } => true,
        HUnary unary => Inert(unary.Operand),
        HBinary binary => HirBuilder.IsPure(binary) && Inert(binary.Left) && Inert(binary.Right),
        HCompare comparison => Inert(comparison.Left) && Inert(comparison.Right),
        HConv conversion => HirBuilder.IsPure(conversion) && Inert(conversion.Operand),
        _ => false,
    };
}
