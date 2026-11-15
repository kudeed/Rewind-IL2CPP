using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Removes values given to a struct variable that nothing ever looks at.
///
/// Machine code sets every local to zero when the method starts, and clears or reuses temporaries after their
/// last use (a struct returned by a call, copied on, and then partly overwritten because its stack memory
/// serves something else from there on). The compiler of the source had no such statements; they only read as
/// uses of the variable - and of members that cannot even be named from this method. A store (of the whole
/// variable or of one field) is removed when on no path from it the variable is read before it is given a new
/// value as a whole, and what was stored has no effect of its own.
/// </summary>
internal static class DeadStores
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_DEAD_STORES") != null;

    private static bool IsStruct(TypeSig? t) => t is { IsValueType: true } and not (PrimitiveSig or PointerSig or ByRefSig or OpaqueSig) && t.Definition is { IsEnum: false };

    /// <summary>The variable a store goes into: the target itself, or the struct variable a chain of struct fields starts at.</summary>
    private static HVar? StoreRoot(HExpr target)
    {
        HExpr e = target;
        while (e is HField { Object: { } owner } && IsStruct(owner.Type)) e = owner;
        return e is HLocal l ? l.Variable : null;
    }

    private static IEnumerable<HBlock> Successors(HBlock block)
    {
        if (block.Statements.Count == 0) yield break;
        switch (block.Statements[^1])
        {
            case HJump j: yield return j.Target; break;
            case HBranch b: yield return b.WhenTrue; yield return b.WhenFalse; break;
            case HSwitch s:
                foreach (HBlock t in s.Targets) yield return t;
                yield return s.Default;
                break;
        }
    }

    /// <summary>
    /// True when the address of the variable (or of a part of it) is used for anything but handing it to a call
    /// that gives no address back: it could then be read through that address, where no statement names it.
    /// </summary>
    private static bool AddressKept(HStmt s, HVar v)
    {
        bool kept = false;
        bool Rooted(HExpr e)
        {
            while (true)
            {
                switch (e)
                {
                    case HLocal l: return ReferenceEquals(l.Variable, v);
                    case HField { Object: { } o }: e = o; continue;
                    default: return false;
                }
            }
        }
        void Walk(HExpr? e, bool handed)
        {
            switch (e)
            {
                case null: return;
                case HAddressOf a:
                    if (!handed && Rooted(a.Target)) kept = true;
                    Walk(a.Target, false);
                    return;
                case HCall call:
                {
                    bool returnsAddress = call.Type is ByRefSig or PointerSig;
                    if (call.This != null)
                    {
                        if (returnsAddress && Rooted(call.This)) kept = true;
                        Walk(call.This, false);
                    }
                    foreach (HExpr a in call.Arguments) Walk(a, !returnsAddress);
                    return;
                }
                case HNewObject n:
                    foreach (HExpr a in n.Arguments) Walk(a, true);
                    return;
                case HField f: Walk(f.Object, false); return;
                case HElement el: Walk(el.Array, false); Walk(el.Index, false); return;
                case HArrayLength len: Walk(len.Array, false); return;
                case HDeref d: Walk(d.Pointer, false); return;
                case HUnary u: Walk(u.Operand, false); return;
                case HBinary b: Walk(b.Left, false); Walk(b.Right, false); return;
                case HCompare c: Walk(c.Left, false); Walk(c.Right, false); return;
                case HConv c: Walk(c.Operand, false); return;
                case HNewArray na: Walk(na.Length, false); return;
                case HTypeExpr t: Walk(t.Operand, false); return;
                case HCachedDelegate cached: Walk(cached.Creation, false); return;
                case HSelect sel: Walk(sel.Condition, false); Walk(sel.WhenTrue, false); Walk(sel.WhenFalse, false); return;
                case HOpaque o:
                    foreach (HExpr a in o.Operands) Walk(a, false);
                    return;
            }
        }
        switch (s)
        {
            case HAssign a: Walk(a.Target, false); Walk(a.Value, false); break;
            case HEval e: Walk(e.Expression, false); break;
            case HReturn r: Walk(r.Value, false); break;
            case HThrow t: Walk(t.Exception, false); break;
            case HBranch b: Walk(b.Condition, false); break;
            case HSwitch sw: Walk(sw.Value, false); break;
        }
        return kept;
    }

    public static void Run(HMethod method)
    {
        if (Disabled || method.Blocks.Count == 0 || method.Blocks.Count > 600) return;
        var candidates = new List<HVar>();
        foreach (HBlock b in method.Blocks)
            foreach (HStmt s in b.Statements)
                if (s is HAssign a && StoreRoot(a.Target) is { } v && IsStruct(v.Type) && HirBuilder.IsPure(a.Value) && !candidates.Contains(v))
                    candidates.Add(v);
        if (candidates.Count == 0 || candidates.Count > 200) return;

        // Where control can go from each block; from protected code also into its handler, at any point.
        var handlers = new Dictionary<HBlock, List<HBlock>>();
        foreach (HBlock b in method.Blocks)
        {
            for (int s = b.Scope, guard = 0; s >= 0 && guard < 64; guard++, s = method.OuterOf(s))
            {
                if ((s & 1) != 0 || !method.TryRegions.TryGetValue(s >> 1, out HTryRegion? r)) continue;
                if (!handlers.TryGetValue(b, out List<HBlock>? list)) handlers[b] = list = [];
                list.Add(r.HandlerEntry);
            }
        }

        bool any = false;
        foreach (HVar v in candidates)
        {
            bool escapes = false, used = false;
            foreach (HBlock b in method.Blocks)
                foreach (HStmt s in b.Statements)
                {
                    escapes |= AddressKept(s, v);
                    used |= s is HAssign a && ReferenceEquals(StoreRoot(a.Target), v) ? ConstructorFolding.Mentions(a.Value, v) : ConstructorFolding.Mentions(s, v);
                }
            if (escapes) continue;

            // Is the variable read later? Worked out backwards, block by block, until nothing changes.
            var liveIn = new Dictionary<HBlock, bool>();
            bool Floor(HBlock b)
            {
                if (!handlers.TryGetValue(b, out List<HBlock>? list)) return false;
                foreach (HBlock h in list)
                    if (liveIn.GetValueOrDefault(h))
                        return true;
                return false;
            }
            bool LiveOut(HBlock b)
            {
                // Where a finally handler goes on is not written in it: anywhere, as far as this goes.
                if (b.Statements.Count != 0 && b.Statements[^1] is HEndFinally) return used;
                foreach (HBlock t in Successors(b))
                    if (liveIn.GetValueOrDefault(t))
                        return true;
                return false;
            }
            bool Before(HStmt s, bool after)
            {
                if (s is HAssign a && ReferenceEquals(StoreRoot(a.Target), v))
                {
                    bool reads = ConstructorFolding.Mentions(a.Value, v);
                    return a.Target is HLocal ? reads : after || reads;
                }
                return after || ConstructorFolding.Mentions(s, v);
            }
            bool changed = true;
            for (int round = 0; changed && round < 200; round++)
            {
                changed = false;
                for (int i = method.Blocks.Count - 1; i >= 0; i--)
                {
                    HBlock b = method.Blocks[i];
                    bool floor = Floor(b), live = LiveOut(b) || floor;
                    for (int k = b.Statements.Count - 1; k >= 0; k--) live = Before(b.Statements[k], live) || floor;
                    if (live != liveIn.GetValueOrDefault(b))
                    {
                        liveIn[b] = live;
                        changed = true;
                    }
                }
            }
            if (changed) continue; // did not settle

            foreach (HBlock b in method.Blocks)
            {
                bool floor = Floor(b), live = LiveOut(b) || floor;
                for (int k = b.Statements.Count - 1; k >= 0; k--)
                {
                    HStmt s = b.Statements[k];
                    if (!live && s is HAssign a && ReferenceEquals(StoreRoot(a.Target), v) && HirBuilder.IsPure(a.Value))
                    {
                        b.Statements.RemoveAt(k);
                        any = true;
                        continue;
                    }
                    live = Before(s, live) || floor;
                }
            }
        }
        if (any) HirCleanup.Run(method);
    }
}
