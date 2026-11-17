using Rewind.Analysis.Hir;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Gives a switch back the values its jump table does not cover.
///
/// A C++ compiler turns "switch (x) { case 0..N }" into a bounds test and a jump table: "if ((uint)x > N) goto
/// otherwise; jump table[x]". Recovered as it is, that is an "if" in front of a switch whose own default is never
/// taken. Behaviour is the same, but the C# decompiler reads one shape only: an iterator's or async method's
/// MoveNext dispatches on its state with a plain switch, and in front of a bounds test the decompiler no longer
/// recognizes the state - it takes it for an ordinary variable, drops the writes that advance it, and the
/// "yield return"s it rebuilds repeat the first one for ever. So the two become one switch again: its cases as the
/// table has them, its default where the bounds test sends the values outside.
/// </summary>
internal static class SwitchRanges
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_SWITCH_RANGES") != null;

    public static void Run(HMethod method)
    {
        if (Disabled) return;
        var ways = new Dictionary<HBlock, int>();
        void Count(HBlock target) => ways[target] = ways.GetValueOrDefault(target) + 1;
        foreach (HBlock block in method.Blocks)
        {
            if (block.Statements.Count == 0) continue;
            switch (block.Statements[^1])
            {
                case HJump j: Count(j.Target); break;
                case HBranch b: Count(b.WhenTrue); Count(b.WhenFalse); break;
                case HSwitch s:
                    foreach (HBlock t in s.Targets) Count(t);
                    Count(s.Default);
                    break;
            }
        }
        foreach (HTryRegion region in method.TryRegions.Values)
        {
            if (region.Entry != null) Count(region.Entry);
            if (region.HandlerEntry != null) Count(region.HandlerEntry);
        }
        if (method.Blocks.Count != 0) Count(method.Blocks[0]);

        foreach (HBlock block in method.Blocks)
        {
            if (block.Statements.Count == 0 || block.Statements[^1] is not HBranch test) continue;
            if (Bounds(test) is not var (value, last, outside, inside)) continue;
            if (ways.GetValueOrDefault(inside) != 1 || inside.Statements.Count != 1 || inside.Statements[0] is not HSwitch table) continue;
            if (table.Targets.Length != last + 1 || !Same(table.Value, value)) continue;
            table.Default = outside;
            block.Statements[^1] = new HJump(inside);
        }
    }

    /// <summary>An unsigned bounds test "x &gt; N": the value tested, N, and where values above it and the others go.</summary>
    private static (HExpr Value, long Last, HBlock Outside, HBlock Inside)? Bounds(HBranch test)
    {
        if (test.Condition is not HCompare c) return null;
        static long? Constant(HExpr e) => e is HConst { Value: int or long or uint or ulong } k ? Convert.ToInt64(k.Value) : null;
        (HExpr Value, long Last, HBlock Outside, HBlock Inside) found;
        if (c.Op == HCompareOp.LtUn && Constant(c.Left) is { } a) found = (c.Right, a, test.WhenTrue, test.WhenFalse);        // N < x
        else if (c.Op == HCompareOp.GtUn && Constant(c.Right) is { } b) found = (c.Left, b, test.WhenTrue, test.WhenFalse);   // x > N
        else if (c.Op == HCompareOp.LeUn && Constant(c.Right) is { } d) found = (c.Left, d, test.WhenFalse, test.WhenTrue);   // x <= N
        else if (c.Op == HCompareOp.GeUn && Constant(c.Left) is { } e) found = (c.Right, e, test.WhenFalse, test.WhenTrue);   // N >= x
        else return null;
        return found.Last is >= 0 and < 1 << 16 ? found : null;
    }

    /// <summary>The same value read twice with nothing between: one variable, one argument, or one field of either.</summary>
    private static bool Same(HExpr a, HExpr b) => (a, b) switch
    {
        (HLocal x, HLocal y) => ReferenceEquals(x.Variable, y.Variable),
        (HArg x, HArg y) => x.Index == y.Index,
        (HField x, HField y) => ReferenceEquals(x.Field, y.Field) && (x.Object == null ? y.Object == null : y.Object != null && Same(x.Object, y.Object)),
        _ => false,
    };
}
