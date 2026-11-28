using Rewind.Analysis.Hir;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Removes what translation leaves behind but nothing reads: variables for machine values that turned out to be
/// meaningless (registers captured "just in case" around a call whose signature was not known yet), and the
/// assignments that fed them.
/// </summary>
public static class HirCleanup
{
    /// <summary>True when two expressions without side effects are written the same way.</summary>
    internal static bool Same(HExpr? a, HExpr? b)
    {
        if (ReferenceEquals(a, b)) return true;
        if (a == null || b == null || a.GetType() != b.GetType()) return false;
        switch (a)
        {
            case HConst x: return Equals(x.Value, ((HConst)b).Value);
            case HLocal x: return ReferenceEquals(x.Variable, ((HLocal)b).Variable);
            case HArg x: return x.Index == ((HArg)b).Index;
            case HField x: return ReferenceEquals(x.Field, ((HField)b).Field) && Same(x.Object, ((HField)b).Object);
            case HArrayLength x: return Same(x.Array, ((HArrayLength)b).Array);
            case HElement x: return Same(x.Array, ((HElement)b).Array) && Same(x.Index, ((HElement)b).Index);
            case HUnary x: return x.Op == ((HUnary)b).Op && Same(x.Operand, ((HUnary)b).Operand);
            case HBinary x: return x.Op == ((HBinary)b).Op && Same(x.Left, ((HBinary)b).Left) && Same(x.Right, ((HBinary)b).Right);
            case HCompare x: return x.Op == ((HCompare)b).Op && Same(x.Left, ((HCompare)b).Left) && Same(x.Right, ((HCompare)b).Right);
            case HConv x: return x.Kind == ((HConv)b).Kind && Same(x.Operand, ((HConv)b).Operand);
            case HTypeExpr x: return x.Op != HTypeOp.Allocate && x.Op == ((HTypeExpr)b).Op && ReferenceEquals(x.Target, ((HTypeExpr)b).Target) && Same(x.Operand, ((HTypeExpr)b).Operand);
            case HDeref x: return Same(x.Pointer, ((HDeref)b).Pointer);
            case HAddressOf x: return Same(x.Target, ((HAddressOf)b).Target);
            default: return false; // calls and allocations are never "the same"
        }
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
    /// Shapes that are artefacts of how type tests compile: the same question asked twice in a row (depth
    /// check, then base class check), and a null check wrapped around "as" (which is null-safe already).
    /// </summary>
    private static bool Simplify(HMethod method)
    {
        bool any = false;
        var predecessors = new Dictionary<HBlock, int>();
        foreach (HBlock block in method.Blocks)
            foreach (HBlock s in Successors(block))
                predecessors[s] = predecessors.GetValueOrDefault(s) + 1;

        foreach (HBlock a in method.Blocks)
        {
            if (a.Statements.Count == 0 || a.Statements[^1] is not HBranch branch) continue;
            if (EquivalentBranches.TryTarget(method, a, out HBlock? common))
            {
                a.Statements[^1] = new HJump(common!) { Address = branch.Address };
                any = true;
                continue;
            }

            // The question asked again with nothing in between has the answer it just had.
            for (int guard = 0; guard < 4; guard++)
            {
                if (branch.WhenFalse.Statements is [HBranch again] && !ReferenceEquals(branch.WhenFalse, a) && branch.WhenFalse.Scope == a.Scope && Same(branch.Condition, again.Condition))
                {
                    branch.WhenFalse = again.WhenFalse;
                    any = true;
                }
                else if (branch.WhenTrue.Statements is [HBranch repeat] && !ReferenceEquals(branch.WhenTrue, a) && branch.WhenTrue.Scope == a.Scope && Same(branch.Condition, repeat.Condition))
                {
                    branch.WhenTrue = repeat.WhenTrue;
                    any = true;
                }
                else break;
            }

            // if (x == null) m = null; else m = x as T;   is   m = x as T;
            if (branch.Condition is not HCompare { Op: HCompareOp.Eq or HCompareOp.Ne } test) continue;
            HExpr? subject = test.Right is HConst { Value: null } ? test.Left : test.Left is HConst { Value: null } ? test.Right : null;
            if (subject == null) continue;
            HBlock whenNull = test.Op == HCompareOp.Eq ? branch.WhenTrue : branch.WhenFalse;
            HBlock otherwise = test.Op == HCompareOp.Eq ? branch.WhenFalse : branch.WhenTrue;
            if (predecessors.GetValueOrDefault(whenNull) != 1 || predecessors.GetValueOrDefault(otherwise) != 1) continue;
            if (whenNull.Statements is not [HAssign { Target: HLocal nullTarget, Value: HConst { Value: null } }, HJump nullJump]) continue;
            if (otherwise.Statements is not [HAssign { Target: HLocal castTarget, Value: HTypeExpr { Op: HTypeOp.IsInst } cast } assign, HJump castJump]) continue;
            if (!ReferenceEquals(nullTarget.Variable, castTarget.Variable) || !ReferenceEquals(nullJump.Target, castJump.Target) || !Same(subject, cast.Operand)) continue;
            a.Statements[^1] = new HAssign(assign.Target, assign.Value) { Address = branch.Address };
            a.Statements.Add(new HJump(castJump.Target) { Address = branch.Address });
            any = true;
        }
        return any;
    }

    private static void RemoveUnreachable(HMethod method)
    {
        if (method.Blocks.Count == 0) return;
        var reached = new HashSet<HBlock> { method.Blocks[0] };
        var work = new Stack<HBlock>();
        work.Push(method.Blocks[0]);
        // A handler is reachable whenever its protected code is.
        var handlers = new Dictionary<HBlock, List<HBlock>>();
        foreach (HTryRegion r in method.TryRegions.Values)
        {
            if (!handlers.TryGetValue(r.Entry, out List<HBlock>? list)) handlers[r.Entry] = list = [];
            list.Add(r.HandlerEntry);
        }
        while (work.Count > 0)
        {
            HBlock block = work.Pop();
            foreach (HBlock s in Successors(block))
                if (reached.Add(s))
                    work.Push(s);
            if (handlers.TryGetValue(block, out List<HBlock>? entered))
                foreach (HBlock h in entered)
                    if (reached.Add(h))
                        work.Push(h);
        }
        foreach (HTryRegion r in method.TryRegions.Values.ToList())
            if (!reached.Contains(r.Entry))
                method.TryRegions.Remove(r.Index);
        if (reached.Count == method.Blocks.Count) return;
        method.Blocks.RemoveAll(b => !reached.Contains(b));
        for (int i = 0; i < method.Blocks.Count; i++) method.Blocks[i].Id = i;
    }

    /// <summary>
    /// Whether the try regions form properly nested statements: each region's code and handler are entered only
    /// at their start (the handler only by an exception), and every other way out of a block leads to the same
    /// scope or to an enclosing one. Null when they do; otherwise what is wrong.
    /// </summary>
    public static string? CheckTryRegions(HMethod method)
    {
        foreach (HBlock b in method.Blocks)
            if (b.Scope >= 0 && !method.TryRegions.ContainsKey(b.Scope >> 1))
                return $"{b} belongs to a try region that was not rebuilt";
        if (method.TryRegions.Count == 0) return null;
        if (method.Blocks.Count != 0 && method.Blocks[0].Scope != -1) return "the method starts inside a try region";
        var outsideEntries = new Dictionary<HBlock, int>();
        foreach (HTryRegion r in method.TryRegions.Values)
        {
            if (r.Entry.Scope != 2 * r.Index) return $"try {r.Index} does not start with its own code";
            if (r.HandlerEntry.Scope != 2 * r.Index + 1) return $"catch {r.Index} does not start with its own code";
            outsideEntries[r.Entry] = 0;
        }
        foreach (HBlock a in method.Blocks)
            foreach (HBlock t in Successors(a))
            {
                if (method.Encloses(t.Scope, a.Scope)) continue; // same scope, or out to an enclosing one
                HTryRegion? entered = method.TryRegions.Values.FirstOrDefault(r => ReferenceEquals(r.Entry, t));
                if (entered == null || entered.Outer != a.Scope) return $"{a} -> {t} enters a try region or handler other than at its start";
                if (a.Statements[^1] is not HJump) return $"{a} enters try {entered.Index} conditionally";
                outsideEntries[t]++;
            }
        foreach (var (entry, count) in outsideEntries)
            if (count != 1) return $"{entry} is entered from outside its try region {count} times";
        return null;
    }

    public static void Run(HMethod method)
    {
        for (int round = 0; round < 6 && Simplify(method); round++) { }
        RemoveUnreachable(method);
        bool changed = true;
        for (int round = 0; changed && round < 8; round++)
        {
            var reads = new Dictionary<HVar, int>();
            void Read(HExpr? e)
            {
                switch (e)
                {
                    case null: return;
                    case HLocal l: reads[l.Variable] = reads.GetValueOrDefault(l.Variable) + 1; return;
                    case HField f: Read(f.Object); return;
                    case HElement el: Read(el.Array); Read(el.Index); return;
                    case HArrayLength len: Read(len.Array); return;
                    case HAddressOf a: Read(a.Target); return;
                    case HDeref d: Read(d.Pointer); return;
                    case HUnary u: Read(u.Operand); return;
                    case HBinary b: Read(b.Left); Read(b.Right); return;
                    case HCompare c: Read(c.Left); Read(c.Right); return;
                    case HConv c: Read(c.Operand); return;
                    case HCall call: Read(call.This); foreach (HExpr a in call.Arguments) Read(a); return;
                    case HNewObject n: foreach (HExpr a in n.Arguments) Read(a); return;
                    case HNewArray na: Read(na.Length); return;
                    case HTypeExpr t: Read(t.Operand); return;
                    case HSelect s: Read(s.Condition); Read(s.WhenTrue); Read(s.WhenFalse); return;
                    case HOpaque o: foreach (HExpr a in o.Operands) Read(a); return;
                }
            }

            foreach (HBlock block in method.Blocks)
            {
                foreach (HStmt s in block.Statements)
                {
                    switch (s)
                    {
                        case HAssign a:
                            // Writing a whole local does not read it; writing through it (a field, an element) does.
                            if (a.Target is not HLocal) Read(a.Target);
                            Read(a.Value);
                            break;
                        case HEval e: Read(e.Expression); break;
                        case HReturn r: Read(r.Value); break;
                        case HThrow t: Read(t.Exception); break;
                        case HBranch b: Read(b.Condition); break;
                        case HSwitch sw: Read(sw.Value); break;
                    }
                }
            }

            changed = false;
            foreach (HBlock block in method.Blocks)
            {
                for (int i = block.Statements.Count - 1; i >= 0; i--)
                {
                    if (block.Statements[i] is not HAssign { Target: HLocal target } assign) continue;
                    if (reads.GetValueOrDefault(target.Variable) != 0) continue;
                    if (HirBuilder.IsPure(assign.Value)) block.Statements.RemoveAt(i);
                    else block.Statements[i] = new HEval(assign.Value) { Address = assign.Address };
                    changed = true;
                }
            }

            if (changed)
            {
                // Removing unused register copies can reveal two metadata-guard paths that now do exactly
                // the same work. Reconsider the control flow before counting the next round's reads.
                for (int again = 0; again < 6 && Simplify(method); again++) { }
                RemoveUnreachable(method);
                continue;
            }
            // Finally drop the declarations of variables that no statement mentions any more.
            var mentioned = new HashSet<HVar>(reads.Keys);
            foreach (HTryRegion r in method.TryRegions.Values) mentioned.Add(r.Exception);
            foreach (HBlock block in method.Blocks)
                foreach (HStmt s in block.Statements)
                    if (s is HAssign { Target: HLocal l })
                        mentioned.Add(l.Variable);
            if (method.Locals.RemoveAll(v => !mentioned.Contains(v)) != 0)
                for (int i = 0; i < method.Locals.Count; i++) method.Locals[i].Index = i;
        }
    }
}
