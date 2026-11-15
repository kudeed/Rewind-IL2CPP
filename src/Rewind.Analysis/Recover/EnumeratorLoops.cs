using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Gives a loop over an enumerator the form the compiler gave it, so that it reads as "foreach" again.
///
/// The compiler writes "foreach (T x in source) body" as: get the enumerator; then, protected by a finally
/// handler that disposes of it, "while (e.MoveNext()) { T x = e.Current; body }". The C++ compiler keeps what
/// that does but not how it is laid out: it pastes "Current" (a field of the enumerator) into every place the
/// element is used, and puts unrelated assignments between getting the enumerator and entering the loop. Both
/// are put back here: the element is read once, where the loop body starts, and the enumerator is the last
/// thing obtained before the protected code.
/// </summary>
internal static class EnumeratorLoops
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_LOOP_SHAPING") != null;

    public static void Run(HMethod method, ProgramAnalysis program)
    {
        if (Disabled || method.TryRegions.Count == 0) return;
        foreach (HTryRegion r in method.TryRegions.Values.OrderBy(r => r.Index).ToList())
        {
            if (!r.Finally || Disposed(method, r) is not { } enumerator) continue;
            OrderEntry(method, r, enumerator);
            OneCurrent(method, r, enumerator, program);
        }
    }

    /// <summary>The variable the region's finally handler disposes of.</summary>
    private static HVar? Disposed(HMethod method, HTryRegion r)
    {
        HVar? found = null;
        foreach (HBlock b in method.Blocks)
        {
            if (b.Scope != 2 * r.Index + 1) continue;
            foreach (HStmt s in b.Statements)
                if (s is HEval { Expression: HCall { This: HLocal { Variable: var v }, Method.Name: "Dispose", Arguments.Length: 0 } })
                {
                    if (found != null && !ReferenceEquals(found, v)) return null;
                    found = v;
                }
        }
        return found;
    }

    /// <summary>A value made of constants and variables alone: it is the same wherever it is computed, as long as those variables are not set in between.</summary>
    private static bool Plain(HExpr e) => e switch
    {
        HConst or HArg => true,
        HLocal l => !l.Variable.AddressTaken,
        HUnary u => Plain(u.Operand),
        HBinary b => HirBuilder.IsPure(b) && Plain(b.Left) && Plain(b.Right),
        HCompare c => Plain(c.Left) && Plain(c.Right),
        HConv c => HirBuilder.IsPure(c) && Plain(c.Operand),
        HTypeExpr { Op: HTypeOp.Default } => true,
        HSelect s => Plain(s.Condition) && Plain(s.WhenTrue) && Plain(s.WhenFalse),
        _ => false,
    };

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
    /// Moves the assignment of the enumerator to the end of the block that enters the protected code, past
    /// assignments of plain values to other variables (the starting values of what the loop computes).
    /// </summary>
    private static void OrderEntry(HMethod method, HTryRegion r, HVar enumerator)
    {
        HBlock? before = null;
        foreach (HBlock b in method.Blocks)
        {
            if (method.Encloses(2 * r.Index, b.Scope)) continue;
            foreach (HBlock t in Successors(b))
                if (ReferenceEquals(t, r.Entry))
                {
                    if (before != null) return;
                    before = b;
                }
        }
        if (before == null || before.Statements[^1] is not HJump) return;

        // Back from there, statement by statement - on into the block before when this one does nothing else
        // (the compiler likes to give the starting values a block of their own).
        HBlock at = before;
        int i = at.Statements.Count - 2;
        var passed = new List<HVar>();
        HAssign? resource = null;
        for (int hops = 0; resource == null;)
        {
            if (i < 0)
            {
                if (++hops > 2) return;
                HBlock? only = null;
                foreach (HBlock b in method.Blocks)
                    foreach (HBlock t in Successors(b))
                        if (ReferenceEquals(t, at))
                        {
                            if (only != null) return;
                            only = b;
                        }
                if (only == null || only.Scope != at.Scope || only.Statements[^1] is not HJump) return;
                at = only;
                i = at.Statements.Count - 2;
                continue;
            }
            if (at.Statements[i] is not HAssign { Target: HLocal target, Value: var value } assign) return;
            if (ReferenceEquals(target.Variable, enumerator))
            {
                resource = assign;
                break;
            }
            if (target.Variable.AddressTaken || !Plain(value) || ConstructorFolding.Mentions(value, enumerator)) return;
            passed.Add(target.Variable);
            i--;
        }
        if (passed.Count == 0) return;
        // What is passed keeps its order; the enumerator's value must not depend on any of it.
        foreach (HVar moved in passed)
            if (ConstructorFolding.Mentions(resource.Value, moved))
                return;
        at.Statements.RemoveAt(i);
        before.Statements.Insert(before.Statements.Count - 1, resource);
    }

    /// <summary>Replaces, everywhere below <paramref name="e"/>, the nodes <paramref name="map"/> gives a replacement for.</summary>
    internal static HExpr Rewrite(HExpr e, Func<HExpr, HExpr?> map)
    {
        if (map(e) is { } replaced) return replaced;
        switch (e)
        {
            case HField f: if (f.Object != null) f.Object = Rewrite(f.Object, map); break;
            case HElement el: el.Array = Rewrite(el.Array, map); el.Index = Rewrite(el.Index, map); break;
            case HArrayLength len: len.Array = Rewrite(len.Array, map); break;
            case HAddressOf a: a.Target = Rewrite(a.Target, map); break;
            case HDeref d: d.Pointer = Rewrite(d.Pointer, map); break;
            case HUnary u: u.Operand = Rewrite(u.Operand, map); break;
            case HBinary b: b.Left = Rewrite(b.Left, map); b.Right = Rewrite(b.Right, map); break;
            case HCompare c: c.Left = Rewrite(c.Left, map); c.Right = Rewrite(c.Right, map); break;
            case HConv c: c.Operand = Rewrite(c.Operand, map); break;
            case HCall call:
                if (call.This != null) call.This = Rewrite(call.This, map);
                for (int i = 0; i < call.Arguments.Length; i++)
                    if (call.Arguments[i] != null)
                        call.Arguments[i] = Rewrite(call.Arguments[i], map);
                break;
            case HNewObject n:
                for (int i = 0; i < n.Arguments.Length; i++)
                    if (n.Arguments[i] != null)
                        n.Arguments[i] = Rewrite(n.Arguments[i], map);
                break;
            case HNewArray na: na.Length = Rewrite(na.Length, map); break;
            case HTypeExpr t: if (t.Operand != null) t.Operand = Rewrite(t.Operand, map); break;
            case HSelect s: s.Condition = Rewrite(s.Condition, map); s.WhenTrue = Rewrite(s.WhenTrue, map); s.WhenFalse = Rewrite(s.WhenFalse, map); break;
            case HOpaque o:
                for (int i = 0; i < o.Operands.Length; i++) o.Operands[i] = Rewrite(o.Operands[i], map);
                break;
        }
        return e;
    }

    internal static void Rewrite(HStmt s, Func<HExpr, HExpr?> map)
    {
        switch (s)
        {
            case HAssign a: a.Target = Rewrite(a.Target, map); a.Value = Rewrite(a.Value, map); break;
            case HEval e: e.Expression = Rewrite(e.Expression, map); break;
            case HReturn r: if (r.Value != null) r.Value = Rewrite(r.Value, map); break;
            case HThrow t: if (t.Exception != null) t.Exception = Rewrite(t.Exception, map); break;
            case HBranch b: b.Condition = Rewrite(b.Condition, map); break;
            case HSwitch sw: sw.Value = Rewrite(sw.Value, map); break;
        }
    }

    private static HVar? Root(HExpr target) => target switch
    {
        HLocal l => l.Variable,
        HField { Object: { } owner } => Root(owner),
        _ => null,
    };

    /// <summary>
    /// Where the loop body reads the enumerator's current element in several places (the property pasted in
    /// each time), reads it once at the start of the body and uses that.
    /// </summary>
    private static void OneCurrent(HMethod method, HTryRegion r, HVar enumerator, ProgramAnalysis program)
    {
        int body = 2 * r.Index;
        bool Inside(HBlock b) => method.Encloses(body, b.Scope);
        bool IsEnumerator(HExpr? e) => e is HLocal l && ReferenceEquals(l.Variable, enumerator);

        // The loop: the one place "MoveNext" is called, deciding where the protected code goes on.
        HBlock? head = null, first = null;
        foreach (HBlock b in method.Blocks)
        {
            if (!Inside(b) || b.Statements.Count == 0 || b.Statements[^1] is not HBranch branch) continue;
            HExpr condition = branch.Condition;
            bool negated = false;
            while (condition is HUnary { Op: HUnaryOp.LogicalNot, Operand: var inner })
            {
                negated = !negated;
                condition = inner;
            }
            if (condition is not HCall { Method.Name: "MoveNext", Arguments.Length: 0 } call || !IsEnumerator(call.This)) continue;
            if (head != null) return;
            head = b;
            first = negated ? branch.WhenFalse : branch.WhenTrue;
        }
        if (head == null || first == null || !Inside(first) || ReferenceEquals(first, head)) return;
        foreach (HBlock b in method.Blocks)
            if (!ReferenceEquals(b, head) && Successors(b).Contains(first))
                return; // the body is entered from elsewhere too

        // Inside the protected code the enumerator is used for that call and for reading the element, nothing else.
        FieldDef? current = null;
        HField? sample = null;
        int reads = 0, mentions = 0;
        bool strange = false;
        foreach (HBlock b in method.Blocks)
        {
            if (!Inside(b)) continue;
            foreach (HStmt s in b.Statements)
            {
                if (s is HAssign a && ReferenceEquals(Root(a.Target), enumerator)) return;
                FinallyFolding.Visit(s, x =>
                {
                    if (IsEnumerator(x)) mentions++;
                    if (x is not HField { Object: var o } f || !IsEnumerator(o)) return;
                    if (current == null && program.Accessors.GetterOf(f.Field) is { Name: "get_Current" }) current = f.Field;
                    if (ReferenceEquals(f.Field, current))
                    {
                        reads++;
                        sample ??= f;
                    }
                    else strange = true;
                });
            }
        }
        if (strange || current == null || sample == null || mentions != reads + 1) return;
        TypeSig? type = sample.Type;
        if (type == null || type.ContainsGenericParameter) return;
        // One read, in the statement the body starts with: that is the form already.
        if (reads == 1 && first.Statements.Count != 0)
        {
            bool there = false;
            FinallyFolding.Visit(first.Statements[0], x => there |= ReferenceEquals(x, sample));
            if (there) return;
        }

        HVar element = method.NewLocal(type, "v");
        foreach (HBlock b in method.Blocks)
        {
            if (!Inside(b)) continue;
            foreach (HStmt s in b.Statements)
                Rewrite(s, x => x is HField { Object: var o } f && ReferenceEquals(f.Field, current) && IsEnumerator(o) ? new HLocal(element) { Type = type } : null);
        }
        var read = new HField { Object = new HLocal(enumerator) { Type = enumerator.Type }, Field = current, DeclaringType = sample.DeclaringType, Type = type };
        first.Statements.Insert(0, new HAssign(new HLocal(element) { Type = type }, read) { Address = first.Statements.Count != 0 ? first.Statements[0].Address : 0 });
    }
}
