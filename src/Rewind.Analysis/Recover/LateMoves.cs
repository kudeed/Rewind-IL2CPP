using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts plain moves where they are used.
///
/// "x = default(S)", "m = 5", "m = other": statements that only give a variable a value that is already there.
/// The compiler does them wherever a register or a moment is free - before the statements of something else,
/// in each branch of a test instead of once after it. Read back in that order they stand in the middle of
/// what belongs together: between the statements of a method that was pasted in (which then is not recognized
/// as that method), between "x = default" and the "x..ctor(...)" it is the first half of.
///
/// A plain move is taken down to the first statement of its block that uses the variable, past statements
/// that neither use the variable nor change what it is given. Where every way into a block ends with the same
/// plain move, it is done once, in that block.
/// </summary>
internal static class LateMoves
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_LATE_MOVES") != null;

    public static bool Run(HMethod method)
    {
        if (Disabled) return false;
        bool any = false;
        for (int round = 0; round < 4; round++)
        {
            bool changed = IntoJoins(method);
            foreach (HBlock block in method.Blocks) changed |= Down(block);
            if (!changed) break;
            any = true;
        }
        return any;
    }

    /// <summary>A variable given a constant, a default value, or what another variable (one nothing points to) holds.</summary>
    private static bool Plain(HStmt s, out HVar variable, out HVar? from)
    {
        variable = null!;
        from = null;
        if (s is not HAssign { Target: HLocal { Variable: var v }, Value: var value }) return false;
        switch (value)
        {
            case HConst:
            case HTypeExpr { Op: HTypeOp.Default, Operand: null }:
                break;
            case HLocal { Variable: var w } when !ReferenceEquals(w, v):
                from = w;
                break;
            default:
                return false;
        }
        variable = v;
        return true;
    }

    private static bool Touches(HStmt s, HVar v)
    {
        bool found = s is HAssign { Target: HLocal { Variable: var set } } && ReferenceEquals(set, v);
        if (!found) FinallyFolding.Visit(s, e => found |= e is HLocal l && ReferenceEquals(l.Variable, v));
        return found;
    }

    private static bool Touches(HExpr e, HVar v)
    {
        bool found = false;
        FinallyFolding.Visit(e, x => found |= x is HLocal l && ReferenceEquals(l.Variable, v));
        return found;
    }

    /// <summary>Nothing in the statement can reach a variable other than by naming it: no call, nothing read or written through a pointer.</summary>
    private static bool Quiet(HStmt s)
    {
        bool quiet = true;
        FinallyFolding.Visit(s, e => quiet &= e is HLocal or HArg or HConst or HField or HElement or HArrayLength or HAddressOf or HUnary or HBinary or
            HCompare or HConv or HSelect or HTypeExpr);
        return quiet;
    }

    /// <summary>Whether the move does the same after the statement as before it.</summary>
    private static bool Passes(HVar variable, HVar? from, HStmt over)
    {
        if (over is not (HAssign or HEval)) return false;
        if (Touches(over, variable)) return false;
        // What the variable is given must be the same afterwards.
        if (from != null)
        {
            if (over is HAssign { Target: var target } && (target is HLocal { Variable: var set } ? ReferenceEquals(set, from) : Touches(target, from))) return false;
            if (from.Type.IsValueType && Touches(over, from) && !Quiet(over)) return false;
            // What something points to can be changed without being named.
            if (from.AddressTaken && !Quiet(over)) return false;
        }
        // A variable something points to can be reached without being named.
        if (variable.AddressTaken && !Quiet(over)) return false;
        return true;
    }

    private static bool Down(HBlock block)
    {
        List<HStmt> s = block.Statements;
        if (s.Count < 3) return false;
        bool changed = false;
        // Each statement once, in the order they stand: what is moved later ends up nearer to its use.
        foreach (HStmt move in s.ToArray())
        {
            if (!Plain(move, out HVar variable, out HVar? from)) continue;
            int i = s.IndexOf(move);
            if (i < 0) continue;
            int j = i;
            bool pastSomething = false;
            while (j + 1 < s.Count - 1 && Passes(variable, from, s[j + 1]))
            {
                j++;
                pastSomething |= !Plain(s[j], out _, out _);
            }
            // Only to where it is used, and only past something that is not just another move.
            if (j == i || !pastSomething || !Touches(s[j + 1], variable)) continue;
            s.RemoveAt(i);
            s.Insert(j, move);
            changed = true;
        }
        return changed;
    }

    private static bool Same(HStmt a, HStmt b) =>
        a is HAssign x && b is HAssign y && HirCleanup.Same(x.Target, y.Target) && HirCleanup.Same(x.Value, y.Value);

    /// <summary>Where a block has the move among its last statements, free to stand at its very end; -1 when it does not.</summary>
    private static int Trailing(HBlock block, HStmt move, HVar variable, HVar? from)
    {
        List<HStmt> s = block.Statements;
        for (int k = s.Count - 2; k >= 0 && k >= s.Count - 9; k--)
        {
            if (s[k] is not HAssign) return -1;
            if (!Same(s[k], move)) continue;
            for (int after = k + 1; after < s.Count - 1; after++)
                if (!Passes(variable, from, s[after]))
                    return -1;
            return k;
        }
        return -1;
    }

    private static bool IntoJoins(HMethod method)
    {
        var ways = new Dictionary<HBlock, List<HBlock>>();
        var barred = new HashSet<HBlock>(); // entered other than by a plain jump
        void Way(HBlock from, HBlock to, bool jump)
        {
            if (!ways.TryGetValue(to, out List<HBlock>? list)) ways[to] = list = [];
            list.Add(from);
            if (!jump) barred.Add(to);
        }
        foreach (HBlock b in method.Blocks)
        {
            if (b.Statements.Count == 0) continue;
            switch (b.Statements[^1])
            {
                case HJump j:
                    Way(b, j.Target, true);
                    break;
                case HBranch br:
                    Way(b, br.WhenTrue, false);
                    Way(b, br.WhenFalse, false);
                    break;
                case HSwitch sw:
                    foreach (HBlock t in sw.Targets) Way(b, t, false);
                    Way(b, sw.Default, false);
                    break;
            }
        }
        foreach (HTryRegion region in method.TryRegions.Values)
        {
            barred.Add(region.Entry);
            barred.Add(region.HandlerEntry);
        }
        if (method.Blocks.Count != 0) barred.Add(method.Blocks[0]);

        bool changed = false;
        foreach (HBlock join in method.Blocks)
        {
            if (barred.Contains(join) || !ways.TryGetValue(join, out List<HBlock>? from) || from.Count < 2) continue;
            if (from.Any(p => ReferenceEquals(p, join) || p.Scope != join.Scope) || from.Distinct().Count() != from.Count) continue;
            for (int guard = 0; guard < 8; guard++)
            {
                HBlock first = from[0];
                HStmt? chosen = null;
                HVar? variable = null, source = null;
                for (int k = first.Statements.Count - 2; k >= 0 && k >= first.Statements.Count - 9; k--)
                {
                    HStmt candidate = first.Statements[k];
                    if (candidate is not HAssign) break;
                    if (!Plain(candidate, out HVar v, out HVar? w)) continue;
                    if (!from.All(p => Trailing(p, candidate, v, w) >= 0)) continue;
                    (chosen, variable, source) = (candidate, v, w);
                    break;
                }
                if (chosen == null) break;
                foreach (HBlock p in from) p.Statements.RemoveAt(Trailing(p, chosen, variable!, source));
                join.Statements.Insert(0, chosen);
                changed = true;
            }
        }
        return changed;
    }
}
