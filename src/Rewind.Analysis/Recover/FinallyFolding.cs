using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts "finally" back.
///
/// IL2CPP writes try/finally as C++: the protected code sits in a C++ try whose handler only keeps the exception;
/// after it comes the clean-up code; and after that, if an exception was kept, it is thrown again. The C++
/// compiler then copies the clean-up code to every way out of the protected code. What the machine code shows
/// is therefore a catch-all that does nothing but keep the exception, the clean-up statements once for each
/// way out, and a re-throw behind the copy the handler leads to. Here that shape is recognised, and the region
/// becomes what it was: protected code with one finally handler, left by whatever followed each copy.
///
/// Nothing is assumed: the handler must do nothing else, every way out of the protected code must run the same
/// statements as the handler's path does, and the kept exception must be used for the re-throw alone. Where
/// any of that does not hold, the catch-all stays - it does the same thing either way.
/// </summary>
internal static class FinallyFolding
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_FINALLY_FOLD") != null;
    private static readonly bool Stats = Environment.GetEnvironmentVariable("REWIND_FINALLY_STATS") != null;
    private static readonly Dictionary<string, (int Count, List<string> Examples)> Outcomes = [];

    static FinallyFolding()
    {
        if (!Stats) return;
        AppDomain.CurrentDomain.ProcessExit += (_, _) =>
        {
            lock (Outcomes)
                foreach (var (outcome, (count, examples)) in Outcomes.OrderByDescending(kv => kv.Value.Count))
                    Console.Error.WriteLine($"finally: {count,6}  {outcome}   e.g. {string.Join(" | ", examples)}");
        };
    }

    private static void Count(string outcome, HMethod method)
    {
        if (!Stats) return;
        lock (Outcomes)
        {
            if (!Outcomes.TryGetValue(outcome, out var entry)) entry = (0, []);
            if (entry.Examples.Count < 4)
            {
                string name = method.Method.DeclaringType.Name + "::" + method.Method.Name;
                if (!entry.Examples.Contains(name)) entry.Examples.Add(name);
            }
            Outcomes[outcome] = (entry.Count + 1, entry.Examples);
        }
    }

    private const string Folded = "folded", Removed = "removed (nothing to clean up)";

    public static void Run(HMethod method, ProgramAnalysis program)
    {
        if (Disabled || method.TryRegions.Count == 0) return;
        int Depth(HTryRegion r)
        {
            int depth = 0;
            for (int s = r.Outer; s >= 0 && depth < 64; s = method.OuterOf(s)) depth++;
            return depth;
        }
        bool any = false;
        // Inner regions first: the clean-up code of an inner one is part of the code around it.
        foreach (HTryRegion r in method.TryRegions.Values.OrderByDescending(Depth).ThenBy(r => r.Index).ToList())
        {
            if (r.Finally || !method.TryRegions.ContainsKey(r.Index)) continue;
            if (TypeCatch(method, r))
            {
                Count("catch given its type", method);
                any = true;
            }
            string outcome = Fold(method, r, program);
            Count(outcome, method);
            any |= outcome is Folded or Removed;
        }
        if (!any) return;
        HirCleanup.Run(method);
        if (HirCleanup.CheckTryRegions(method) is { } broken) method.Problems.Add("finally not rebuilt: " + broken);
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

    private static void Retarget(HBlock from, HBlock old, HBlock replacement)
    {
        switch (from.Statements[^1])
        {
            case HJump j:
                if (ReferenceEquals(j.Target, old)) j.Target = replacement;
                break;
            case HBranch b:
                if (ReferenceEquals(b.WhenTrue, old)) b.WhenTrue = replacement;
                if (ReferenceEquals(b.WhenFalse, old)) b.WhenFalse = replacement;
                break;
            case HSwitch s:
                for (int i = 0; i < s.Targets.Length; i++)
                    if (ReferenceEquals(s.Targets[i], old)) s.Targets[i] = replacement;
                if (ReferenceEquals(s.Default, old)) s.Default = replacement;
                break;
        }
    }

    private static bool IsNothing(HExpr e) => e is HConst { Value: null or 0 or 0L };

    /// <summary>"x != null" (whenSet true) or "x == null" (false), however it is written.</summary>
    private static bool NullTest(HExpr condition, out HExpr subject, out bool whenSet)
    {
        subject = condition;
        whenSet = true;
        bool negated = false;
        while (condition is HUnary { Op: HUnaryOp.LogicalNot, Operand: var inner })
        {
            negated = !negated;
            condition = inner;
        }
        if (condition is not HCompare { Op: HCompareOp.Eq or HCompareOp.Ne } test) return false;
        if (IsNothing(test.Right)) subject = test.Left;
        else if (IsNothing(test.Left)) subject = test.Right;
        else return false;
        whenSet = (test.Op == HCompareOp.Ne) != negated;
        return true;
    }

    internal static void Visit(HExpr? e, Action<HExpr> visit)
    {
        if (e == null) return;
        visit(e);
        switch (e)
        {
            case HField f: Visit(f.Object, visit); break;
            case HElement el: Visit(el.Array, visit); Visit(el.Index, visit); break;
            case HArrayLength len: Visit(len.Array, visit); break;
            case HAddressOf a: Visit(a.Target, visit); break;
            case HDeref d: Visit(d.Pointer, visit); break;
            case HUnary u: Visit(u.Operand, visit); break;
            case HBinary b: Visit(b.Left, visit); Visit(b.Right, visit); break;
            case HCompare c: Visit(c.Left, visit); Visit(c.Right, visit); break;
            case HConv c: Visit(c.Operand, visit); break;
            case HCall call:
                Visit(call.This, visit);
                foreach (HExpr a in call.Arguments) Visit(a, visit);
                break;
            case HNewObject n:
                foreach (HExpr a in n.Arguments) Visit(a, visit);
                break;
            case HNewArray na: Visit(na.Length, visit); break;
            case HTypeExpr t: Visit(t.Operand, visit); break;
            case HCachedDelegate cached: Visit(cached.Creation, visit); break;
            case HSelect s: Visit(s.Condition, visit); Visit(s.WhenTrue, visit); Visit(s.WhenFalse, visit); break;
            case HOpaque o:
                foreach (HExpr a in o.Operands) Visit(a, visit);
                break;
        }
    }

    internal static void Visit(HStmt s, Action<HExpr> visit)
    {
        switch (s)
        {
            case HAssign a: Visit(a.Target, visit); Visit(a.Value, visit); break;
            case HEval e: Visit(e.Expression, visit); break;
            case HReturn r: Visit(r.Value, visit); break;
            case HThrow t: Visit(t.Exception, visit); break;
            case HBranch b: Visit(b.Condition, visit); break;
            case HSwitch sw: Visit(sw.Value, visit); break;
        }
    }

    /// <summary>
    /// True when nothing in the block can raise an exception as far as the C++ compiler is concerned: no call
    /// of any kind (an allocation, a cast and a throw are calls too). The compiler keeps track of the protected
    /// region only where something can be thrown; code like this may lie outside it and still belong to it.
    /// </summary>
    private static bool CannotThrow(HBlock block)
    {
        bool calls = false;
        foreach (HStmt s in block.Statements)
        {
            if (s is not (HAssign or HJump or HBranch or HSwitch)) return false;
            Visit(s, e => calls |= e is HCall or HNewObject or HNewArray or HOpaque or HCachedDelegate ||
                                   e is HTypeExpr { Op: HTypeOp.Allocate or HTypeOp.Box or HTypeOp.CastClass or HTypeOp.UnboxAny });
        }
        return !calls && block.Statements.Count != 0;
    }

    /// <summary>
    /// "catch (T e)" is compiled as a catch of everything that starts by testing for T and throwing the
    /// exception on when it is something else. Gives the region its type and takes the test out.
    /// </summary>
    private static bool TypeCatch(HMethod method, HTryRegion r)
    {
        HBlock h = r.HandlerEntry;
        HVar caught = r.Exception;
        if (h.Statements.Count is not (1 or 2) || h.Statements[^1] is not HBranch branch) return false;
        HExpr condition = branch.Condition;
        bool negated = false;
        while (condition is HUnary { Op: HUnaryOp.LogicalNot, Operand: var inner })
        {
            negated = !negated;
            condition = inner;
        }
        if (h.Statements.Count == 2)
        {
            // The answer goes through a temporary nothing else looks at.
            if (h.Statements[0] is not HAssign { Target: HLocal { Variable: var answer }, Value: var value } || condition is not HLocal { Variable: var asked } ||
                !ReferenceEquals(answer, asked))
                return false;
            int mentions = 0;
            foreach (HBlock b in method.Blocks)
                foreach (HStmt s in b.Statements)
                    Visit(s, e => mentions += e is HLocal l && ReferenceEquals(l.Variable, answer) ? 1 : 0);
            if (mentions != 2) return false;
            condition = value;
        }
        if (!NullTest(condition, out HExpr subject, out bool whenSet)) return false;
        if (subject is not HTypeExpr { Op: HTypeOp.IsInst, Operand: HLocal { Variable: var tested }, Target: var type } || !ReferenceEquals(tested, caught)) return false;
        if (negated) whenSet = !whenSet;
        HBlock matches = whenSet ? branch.WhenTrue : branch.WhenFalse, otherwise = whenSet ? branch.WhenFalse : branch.WhenTrue;
        if (otherwise.Scope != h.Scope || otherwise.Statements is not [HThrow { Exception: null }]) return false;
        if (type.IsValueType || type.ContainsGenericParameter) return false;

        ulong address = branch.Address;
        h.Statements.Clear();
        h.Statements.Add(new HJump(matches) { Address = address });
        if (!ReferenceEquals(caught.Type, type))
        {
            caught.Type = type;
            foreach (HBlock b in method.Blocks)
                foreach (HStmt s in b.Statements)
                    Visit(s, e =>
                    {
                        if (e is HLocal l && ReferenceEquals(l.Variable, caught)) l.Type = type;
                    });
        }
        return true;
    }

    private static string Fold(HMethod method, HTryRegion r, ProgramAnalysis program)
    {
        int body = 2 * r.Index, handlerScope = body + 1, outer = r.Outer;
        HVar caught = r.Exception;

        // The handler: one block that keeps the exception (unless it is used as it is), sets merged values for
        // where it goes, and goes there.
        if (method.TryRegions.Values.Any(q => q.Outer == handlerScope)) return "handler holds a try";
        HBlock? handler = null;
        foreach (HBlock b in method.Blocks)
        {
            if (b.Scope != handlerScope) continue;
            if (handler != null) return "handler of several blocks";
            handler = b;
        }
        if (handler == null || !ReferenceEquals(handler, r.HandlerEntry)) return "handler missing";
        if (handler.Statements.Count == 0 || handler.Statements[^1] is not HJump { Target: var x }) return "handler of several blocks";
        if (x.Scope != outer) return "handler leaves to another scope";
        HVar? slot = null;
        var edge = new List<HVar>();
        for (int i = 0; i < handler.Statements.Count - 1; i++)
        {
            if (handler.Statements[i] is not HAssign { Target: HLocal target, Value: var value }) return "handler acts";
            if (value is HLocal { Variable: var v } && ReferenceEquals(v, caught))
            {
                if (slot != null) return "handler acts";
                slot = target.Variable;
            }
            else if (ConstructorFolding.Mentions(value, caught) || !HirBuilder.IsPure(value)) return "handler acts";
            else edge.Add(target.Variable);
        }

        var temps = new HashSet<HVar>();
        bool Kept(HExpr? value) => value is HLocal l && (ReferenceEquals(l.Variable, caught) || ReferenceEquals(l.Variable, slot) || temps.Contains(l.Variable));
        bool Touches(HStmt s) => ConstructorFolding.Mentions(s, caught) || (slot != null && ConstructorFolding.Mentions(s, slot));

        // The clean-up code: everything from where the handler goes up to the first look at the kept exception.
        var cleanup = new List<HBlock>();
        HBlock? test = null;
        int cut = 0;
        var seen = new HashSet<HBlock>();
        var work = new Stack<HBlock>();
        work.Push(x);
        while (work.Count > 0)
        {
            HBlock b = work.Pop();
            if (!seen.Add(b)) continue;
            if (b.Scope != outer) return "clean-up code spans scopes";
            int at = b.Statements.FindIndex(Touches);
            if (at >= 0)
            {
                if (test != null) return "exception looked at in several places";
                test = b;
                cut = at;
                continue;
            }
            if (cleanup.Count >= 48) return "clean-up code too long";
            cleanup.Add(b);
            if (b.Statements.Count == 0 || b.Statements[^1] is not (HJump or HBranch or HSwitch)) return "clean-up code ends by itself";
            foreach (HBlock s in Successors(b)) work.Push(s);
        }
        if (test == null) return "exception not thrown again";

        // From there on: the exception is thrown again, and nothing else is done with it.
        for (int i = cut; i < test.Statements.Count - 1; i++)
        {
            if (test.Statements[i] is HAssign { Target: HLocal t, Value: var v } && Kept(v)) temps.Add(t.Variable);
            else return "exception used";
        }
        bool Rethrows(HBlock block)
        {
            for (int i = 0; i < block.Statements.Count - 1; i++)
            {
                if (block.Statements[i] is HAssign { Target: HLocal t, Value: var v } && Kept(v)) temps.Add(t.Variable);
                else return false;
            }
            return block.Statements.Count != 0 && block.Statements[^1] is HThrow { Exception: { } thrown } && Kept(thrown);
        }
        HBlock? continuation = null;
        switch (test.Statements[^1])
        {
            case HThrow { Exception: { } thrown } when Kept(thrown):
                break;
            case HBranch branch when NullTest(branch.Condition, out HExpr subject, out bool whenSet) && Kept(subject):
                continuation = whenSet ? branch.WhenFalse : branch.WhenTrue;
                if (!Rethrows(whenSet ? branch.WhenTrue : branch.WhenFalse)) return "exception used";
                break;
            default:
                return "exception used";
        }

        var predecessors = new Dictionary<HBlock, List<HBlock>>();
        foreach (HBlock b in method.Blocks)
            foreach (HBlock s in Successors(b))
            {
                if (!predecessors.TryGetValue(s, out List<HBlock>? list)) predecessors[s] = list = [];
                list.Add(b);
            }
        bool InBody(HBlock b) => method.Encloses(body, b.Scope);
        var inside = new HashSet<HBlock>(cleanup) { test };

        // The clean-up statements themselves.
        var originals = new List<HStmt>();
        foreach (HBlock b in cleanup) originals.AddRange(b.Statements);
        for (int i = 0; i < cut; i++) originals.Add(test.Statements[i]);
        foreach (HVar v in edge)
            if (originals.Any(s => ConstructorFolding.Mentions(s, v)))
                return "clean-up code depends on how it is reached";
        var assigned = new HashSet<HVar>();
        foreach (HStmt s in originals)
            if (s is HAssign { Target: HLocal l })
                assigned.Add(l.Variable);

        // The protected code, and every way out of it. Each way out begins with the clean-up statements - or is
        // more of the protected code: the C++ compiler keeps track of the region only where something can be
        // thrown, so statements that cannot throw (the top of a loop body, say) may lie outside what its tables
        // say although control goes back in. Such blocks are taken in.
        var region = new HashSet<HBlock>();
        foreach (HBlock b in method.Blocks)
            if (InBody(b))
                region.Add(b);
        var grown = new List<HBlock>();
        var absorbed = new List<HTryRegion>();
        var leaves = new Dictionary<HBlock, Copy?>();
        var exits = new List<(HBlock From, HBlock To)>();
        for (int round = 0; ; round++)
        {
            if (round > 200) return "protected code not delimited";
            exits.Clear();
            var more = new List<HBlock>();
            foreach (HBlock b in region)
                foreach (HBlock t in Successors(b))
                {
                    if (region.Contains(t)) continue;
                    exits.Add((b, t));
                    if (leaves.ContainsKey(t) || more.Contains(t)) continue;
                    if (ReferenceEquals(t, x))
                    {
                        leaves[t] = null;
                        continue;
                    }
                    if (t.Scope == outer)
                    {
                        var candidate = new Copy(test, cut, assigned);
                        if (candidate.Match(t, x) && (candidate.Shared ? candidate.TestCopy == null : candidate.TestCopy != null))
                        {
                            leaves[t] = candidate;
                            continue;
                        }
                    }
                    more.Add(t);
                }
            if (more.Count == 0) break;
            foreach (HBlock t in more)
            {
                if (t.Scope == outer)
                {
                    if (inside.Contains(t) || !CannotThrow(t)) return "ways out differ";
                    region.Add(t);
                    grown.Add(t);
                }
                else if (method.TryRegions.Values.FirstOrDefault(q => ReferenceEquals(q.Entry, t) && q.Outer == outer) is { } nested)
                {
                    // A whole try statement that the code taken in leads into.
                    absorbed.Add(nested);
                    foreach (HBlock b in method.Blocks)
                        if (method.Encloses(2 * nested.Index, b.Scope) || method.Encloses(2 * nested.Index + 1, b.Scope))
                            region.Add(b);
                }
                else return "protected code leaves several scopes at once";
            }
        }
        foreach (HBlock b in region)
            if (b.Statements.Count != 0 && b.Statements[^1] is HReturn)
                return "protected code returns directly";

        // Where it is entered: once, from outside.
        HBlock entry = r.Entry;
        if (grown.Count != 0)
        {
            HBlock? from = null;
            int ways = 0;
            foreach (HBlock b in method.Blocks)
            {
                if (region.Contains(b) || ReferenceEquals(b, handler)) continue;
                foreach (HBlock t in Successors(b))
                {
                    if (!region.Contains(t)) continue;
                    ways++;
                    from = b;
                    entry = t;
                }
            }
            if (ways != 1 || from!.Scope != outer || from.Statements[^1] is not HJump) return "protected code entered in several places";
            if (!ReferenceEquals(entry, r.Entry) && !grown.Contains(entry)) return "protected code entered in several places";
        }

        // Where each way out goes on once the clean-up code is no longer its own business.
        var onward = new Dictionary<HBlock, (HBlock Block, int At)>();
        var copies = new HashSet<HBlock>();
        foreach (var (t, found) in leaves)
        {
            if (found == null || found.Shared)
            {
                // The same statements serve both ways: the kept exception is null on this one.
                if (continuation == null || slot == null) return "shared clean-up code without a way on";
                if (found == null)
                {
                    onward[t] = (continuation, 0);
                    continue;
                }
            }
            Copy copy = found;
            copies.UnionWith(copy.Blocks);
            foreach (HBlock c in copy.Blocks)
                foreach (HBlock p in predecessors.GetValueOrDefault(c) ?? [])
                {
                    if (copy.Blocks.Contains(p) && !ReferenceEquals(p, copy.TestCopy)) continue;
                    if (ReferenceEquals(c, t) && region.Contains(p)) continue;
                    // The copy's last block may be shared with what follows it when no clean-up statement is in it.
                    if (ReferenceEquals(c, copy.TestCopy) && cut == 0) continue;
                    return "copy of the clean-up code entered from elsewhere";
                }
            // A temporary of the copy must not be needed after it: the handler's statements set their own.
            foreach (var (original, renamed) in copy.Names)
            {
                if (ReferenceEquals(original, renamed)) continue;
                foreach (HBlock b in method.Blocks)
                    for (int i = 0; i < b.Statements.Count; i++)
                        if (!copy.Statements.Contains(b.Statements[i]) && ConstructorFolding.Mentions(b.Statements[i], renamed))
                            return "copy of the clean-up code feeds later code";
            }
            // (A copy that runs into the handler's own statements part of the way shares the rest with them.)
            onward[t] = copy.Shared ? (continuation!, 0) : (copy.TestCopy!, cut);
        }
        foreach (HBlock b in inside)
            foreach (HBlock p in predecessors.GetValueOrDefault(b) ?? [])
            {
                if (inside.Contains(p) && !ReferenceEquals(p, test)) continue;
                if (ReferenceEquals(b, x) && (ReferenceEquals(p, handler) || region.Contains(p))) continue;
                if (copies.Contains(p)) continue;
                return "clean-up code entered from elsewhere";
            }

        // ---- nothing can fail from here on ----

        var rest = new Dictionary<HBlock, HBlock>();
        foreach (var (t, (block, at)) in onward)
        {
            if (at == 0)
            {
                rest[t] = block;
                continue;
            }
            var tail = new HBlock { Id = method.Blocks.Count, Scope = block.Scope };
            tail.Statements.AddRange(block.Statements.Skip(at));
            method.Blocks.Add(tail);
            block.Statements.RemoveRange(at, block.Statements.Count - at);
            block.Statements.Add(new HJump(tail));
            rest[t] = tail;
        }
        foreach (var (from, to) in exits) Retarget(from, to, rest[to]);
        foreach (HBlock b in grown) b.Scope = body;
        foreach (HTryRegion q in absorbed) q.Outer = body;
        r.Entry = entry;

        method.Blocks.Remove(handler);
        if (cleanup.Count == 0 && cut == 0)
        {
            // Nothing is cleaned up (an empty Dispose, pasted in): the region protects nothing.
            foreach (HBlock b in method.Blocks)
                if (b.Scope == body)
                    b.Scope = outer;
            foreach (HTryRegion q in method.TryRegions.Values)
                if (q.Outer == body)
                    q.Outer = outer;
            method.TryRegions.Remove(r.Index);
            for (int i = 0; i < method.Blocks.Count; i++) method.Blocks[i].Id = i;
            return Removed;
        }

        foreach (HBlock b in cleanup) b.Scope = handlerScope;
        ulong address = test.Statements[^1].Address;
        test.Statements.RemoveRange(cut, test.Statements.Count - cut);
        test.Statements.Add(new HEndFinally { Address = address });
        test.Scope = handlerScope;
        r.HandlerEntry = x;
        r.Finally = true;
        for (int i = 0; i < method.Blocks.Count; i++) method.Blocks[i].Id = i;

        // Disposing of a struct in a finally handler is how "foreach" and "using" end: written as a call through
        // IDisposable on the variable itself, which is how the compiler writes it.
        MethodDef? dispose = program.Model.FindType("System.IDisposable")?.Methods.FirstOrDefault(m => m.Name == "Dispose" && m.Parameters.Length == 0);
        if (dispose != null)
            foreach (HBlock b in inside)
                foreach (HStmt s in b.Statements)
                {
                    if (s is not HEval { Expression: HCall { This: HLocal { Type: { } receiver }, Constrained: null } call }) continue;
                    MethodDef m = call.Method;
                    if (m.Name != "Dispose" || m.IsStatic || m.Parameters.Length != 0 || !m.ReturnType.IsVoid || !m.DeclaringType.IsValueType) continue;
                    if (!m.DeclaringType.Interfaces.Any(i => ReferenceEquals(i.Definition, dispose.DeclaringType))) continue;
                    call.Constrained = call.DeclaringType ?? receiver;
                    call.Method = dispose;
                    call.DeclaringType = null;
                    call.Virtual = true;
                    call.Alternatives.Clear();
                }
        return Folded;
    }

    /// <summary>
    /// One copy of the clean-up code, compared with the statements the handler leads to: the same statements in
    /// the same arrangement, where temporaries set inside may have other names.
    /// </summary>
    private sealed class Copy(HBlock test, int cut, HashSet<HVar> assigned)
    {
        private readonly Dictionary<HBlock, HBlock> _pair = [];
        public readonly HashSet<HBlock> Blocks = [];
        public readonly Dictionary<HVar, HVar> Names = [];
        private readonly Dictionary<HVar, HVar> _back = [];
        public readonly HashSet<HStmt> Statements = [];
        public HBlock? TestCopy;
        /// <summary>Set when the copy runs into the statements it is compared with: from there on the two are one.</summary>
        public bool Shared;

        public bool Match(HBlock copy, HBlock original)
        {
            if (_pair.TryGetValue(original, out HBlock? known)) return ReferenceEquals(known, copy);
            if (ReferenceEquals(copy, original))
            {
                _pair[original] = copy;
                Shared = true;
                return true;
            }
            if (!Blocks.Add(copy) || copy.Scope != original.Scope) return false;
            _pair[original] = copy;
            if (ReferenceEquals(original, test))
            {
                if (copy.Statements.Count <= cut) return false;
                for (int i = 0; i < cut; i++)
                    if (!Statement(original.Statements[i], copy.Statements[i]))
                        return false;
                TestCopy = copy;
                return true;
            }
            if (copy.Statements.Count != original.Statements.Count) return false;
            int last = original.Statements.Count - 1;
            for (int i = 0; i < last; i++)
                if (!Statement(original.Statements[i], copy.Statements[i]))
                    return false;
            Statements.Add(copy.Statements[last]);
            switch (original.Statements[last], copy.Statements[last])
            {
                case (HJump a, HJump b):
                    return Match(b.Target, a.Target);
                case (HBranch a, HBranch b):
                    return Expression(a.Condition, b.Condition) && Match(b.WhenTrue, a.WhenTrue) && Match(b.WhenFalse, a.WhenFalse);
                case (HSwitch a, HSwitch b):
                    if (a.Targets.Length != b.Targets.Length || !Expression(a.Value, b.Value)) return false;
                    for (int i = 0; i < a.Targets.Length; i++)
                        if (!Match(b.Targets[i], a.Targets[i]))
                            return false;
                    return Match(b.Default, a.Default);
                default:
                    return false;
            }
        }

        private bool Statement(HStmt original, HStmt copy)
        {
            Statements.Add(copy);
            switch (original, copy)
            {
                case (HAssign a, HAssign b): return Expression(a.Target, b.Target) && Expression(a.Value, b.Value);
                case (HEval a, HEval b): return Expression(a.Expression, b.Expression);
                default: return false;
            }
        }

        private bool Variable(HVar original, HVar copy)
        {
            if (Names.TryGetValue(original, out HVar? known)) return ReferenceEquals(known, copy);
            if (_back.ContainsKey(copy)) return false;
            if (!ReferenceEquals(original, copy) && (!assigned.Contains(original) || !ReferenceEquals(original.Type, copy.Type))) return false;
            Names[original] = copy;
            _back[copy] = original;
            return true;
        }

        private bool All(HExpr[] a, HExpr[] b)
        {
            if (a.Length != b.Length) return false;
            for (int i = 0; i < a.Length; i++)
                if (!Expression(a[i], b[i]))
                    return false;
            return true;
        }

        private static bool Same(TypeSig[] a, TypeSig[] b)
        {
            if (a.Length != b.Length) return false;
            for (int i = 0; i < a.Length; i++)
                if (!ReferenceEquals(a[i], b[i]))
                    return false;
            return true;
        }

        private bool Expression(HExpr? a, HExpr? b)
        {
            if (a == null || b == null) return a == null && b == null;
            if (a.GetType() != b.GetType()) return false;
            switch (a)
            {
                case HConst x: return Equals(x.Value, ((HConst)b).Value);
                case HLocal x: return Variable(x.Variable, ((HLocal)b).Variable);
                case HArg x: return x.Index == ((HArg)b).Index;
                case HField x: return ReferenceEquals(x.Field, ((HField)b).Field) && ReferenceEquals(x.DeclaringType, ((HField)b).DeclaringType) && Expression(x.Object, ((HField)b).Object);
                case HElement x: return Expression(x.Array, ((HElement)b).Array) && Expression(x.Index, ((HElement)b).Index);
                case HArrayLength x: return Expression(x.Array, ((HArrayLength)b).Array);
                case HAddressOf x: return Expression(x.Target, ((HAddressOf)b).Target);
                case HDeref x: return ReferenceEquals(x.Type, b.Type) && Expression(x.Pointer, ((HDeref)b).Pointer);
                case HUnary x: return x.Op == ((HUnary)b).Op && Expression(x.Operand, ((HUnary)b).Operand);
                case HBinary x: return x.Op == ((HBinary)b).Op && Expression(x.Left, ((HBinary)b).Left) && Expression(x.Right, ((HBinary)b).Right);
                case HCompare x: return x.Op == ((HCompare)b).Op && Expression(x.Left, ((HCompare)b).Left) && Expression(x.Right, ((HCompare)b).Right);
                case HConv x: return x.Kind == ((HConv)b).Kind && ReferenceEquals(x.Type, b.Type) && Expression(x.Operand, ((HConv)b).Operand);
                case HCall x:
                {
                    var y = (HCall)b;
                    return ReferenceEquals(x.Method, y.Method) && ReferenceEquals(x.DeclaringType, y.DeclaringType) && x.Virtual == y.Virtual &&
                           ReferenceEquals(x.Constrained, y.Constrained) && Same(x.MethodArguments, y.MethodArguments) &&
                           Expression(x.This, y.This) && All(x.Arguments, y.Arguments);
                }
                case HNewObject x:
                {
                    var y = (HNewObject)b;
                    return ReferenceEquals(x.Constructor, y.Constructor) && ReferenceEquals(x.DeclaringType, y.DeclaringType) && All(x.Arguments, y.Arguments);
                }
                case HNewArray x: return ReferenceEquals(x.ElementType, ((HNewArray)b).ElementType) && Expression(x.Length, ((HNewArray)b).Length);
                case HTypeExpr x: return x.Op == ((HTypeExpr)b).Op && ReferenceEquals(x.Target, ((HTypeExpr)b).Target) && Expression(x.Operand, ((HTypeExpr)b).Operand);
                case HMethodPointer x:
                {
                    var y = (HMethodPointer)b;
                    return ReferenceEquals(x.Method, y.Method) && ReferenceEquals(x.DeclaringType, y.DeclaringType) && Same(x.MethodArguments, y.MethodArguments) &&
                           Expression(x.VirtualOn, y.VirtualOn);
                }
                case HMemberToken x:
                {
                    var y = (HMemberToken)b;
                    return ReferenceEquals(x.Method, y.Method) && ReferenceEquals(x.Field, y.Field) && ReferenceEquals(x.DeclaringType, y.DeclaringType) &&
                           Same(x.MethodArguments, y.MethodArguments);
                }
                case HCachedDelegate x: return Expression(x.Cache, ((HCachedDelegate)b).Cache) && Expression(x.Creation, ((HCachedDelegate)b).Creation);
                case HSelect x:
                    return Expression(x.Condition, ((HSelect)b).Condition) && Expression(x.WhenTrue, ((HSelect)b).WhenTrue) && Expression(x.WhenFalse, ((HSelect)b).WhenFalse);
                case HOpaque x: return x.Text == ((HOpaque)b).Text && All(x.Operands, ((HOpaque)b).Operands);
                default: return false;
            }
        }
    }
}
