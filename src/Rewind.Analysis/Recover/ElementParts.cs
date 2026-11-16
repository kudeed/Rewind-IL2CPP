using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// A struct handed to a method that was pasted in, where the pasted code stores it on one path and passes it on
/// along the other ("list.Add(item)": into the array if there is room, else on to the method that makes room).
///
/// The machine code does not keep such a struct in one piece. On the path that stores it, each part goes from
/// its register straight to where it is stored; only the path that passes it on puts the parts together in
/// memory first. One path then reads "items[n].a = x; items[n].b = y" and the other "item.a = x; item.b = y;
/// AddWithResize(item)", and nothing in the first is the argument the method was called with.
///
/// Where the parts stored on the one path are the parts put together on the other, value for value, and are all
/// of the struct, the struct is put together before the two paths part and the first path stores it whole. That
/// is the pasted method's own shape again, which InlineFolding knows.
/// </summary>
internal static class ElementParts
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_ELEMENT_PARTS") != null;

    public static bool Run(HMethod method)
    {
        if (Disabled) return false;
        Dictionary<HBlock, int>? entries = null;
        bool any = false;
        for (int index = 0; index < method.Blocks.Count; index++)
        {
            HBlock head = method.Blocks[index];
            if (head.Statements.Count == 0 || head.Statements[^1] is not HBranch branch || ReferenceEquals(branch.WhenTrue, branch.WhenFalse)) continue;
            entries ??= Entries(method);
            if (TryJoin(method, head, branch, branch.WhenTrue, branch.WhenFalse, entries) ||
                TryJoin(method, head, branch, branch.WhenFalse, branch.WhenTrue, entries))
                any = true;
        }
        return any;
    }

    /// <summary>From how many places each block is entered.</summary>
    private static Dictionary<HBlock, int> Entries(HMethod method)
    {
        var count = new Dictionary<HBlock, int>();
        void Add(HBlock b) => count[b] = count.GetValueOrDefault(b) + 1;
        foreach (HBlock b in method.Blocks)
        {
            if (b.Statements.Count == 0) continue;
            switch (b.Statements[^1])
            {
                case HJump j: Add(j.Target); break;
                case HBranch br: Add(br.WhenTrue); Add(br.WhenFalse); break;
                case HSwitch s:
                    foreach (HBlock t in s.Targets) Add(t);
                    Add(s.Default);
                    break;
            }
        }
        // (Entered in ways no statement shows: the start of the method, of protected code, of a handler.)
        if (method.Blocks.Count != 0) Add(method.Blocks[0]);
        foreach (HTryRegion r in method.TryRegions.Values)
        {
            Add(r.Entry);
            Add(r.HandlerEntry);
        }
        return count;
    }

    /// <summary>The fields a place is reached through, outermost first, and what they are fields of.</summary>
    private static List<FieldDef> Path(HExpr target, out HExpr root)
    {
        var path = new List<FieldDef>();
        while (target is HField { Object: { } owner } f && !f.Field.IsStatic)
        {
            path.Add(f.Field);
            target = owner;
        }
        path.Reverse();
        root = target;
        return path;
    }

    private static bool SamePath(List<FieldDef> a, List<FieldDef> b)
    {
        if (a.Count != b.Count) return false;
        for (int i = 0; i < a.Count; i++)
            if (!ReferenceEquals(a[i], b[i])) return false;
        return true;
    }

    /// <summary>
    /// A value that is the same on either path: made of constants, variables and parts of struct variables only
    /// (nothing on the paths assigns a variable: see TryJoin), with nothing in it that can fail.
    /// </summary>
    private static bool Fixed(HExpr? e) => e switch
    {
        HConst or HLocal => true,
        HArg a => a.Type is not (ByRefSig or PointerSig),
        HField { Object: { } o } f => !f.Field.IsStatic && o.Type is { IsValueType: true } and not (ByRefSig or PointerSig) && Fixed(o),
        HUnary u => Fixed(u.Operand),
        HBinary b => HirBuilder.IsPure(b) && Fixed(b.Left) && Fixed(b.Right),
        HCompare c => Fixed(c.Left) && Fixed(c.Right),
        HConv c => HirBuilder.IsPure(c) && Fixed(c.Operand),
        _ => false,
    };

    private static bool Alike(HExpr a, HExpr b)
    {
        // A struct made from such values ("new Vector3(x, y, z)") is one too.
        if (a is HNewObject x && b is HNewObject y)
        {
            if (!ReferenceEquals(x.Constructor, y.Constructor) || x.Type is not { IsValueType: true } || x.Arguments.Length != y.Arguments.Length) return false;
            for (int i = 0; i < x.Arguments.Length; i++)
                if (!Alike(x.Arguments[i], y.Arguments[i])) return false;
            return true;
        }
        return Fixed(a) && HirCleanup.Same(a, b);
    }

    /// <summary>Whether the places stored to are, together, all of a value of the type (below the fields already gone through).</summary>
    private static bool Covers(TypeDef? type, List<List<FieldDef>> paths, int depth)
    {
        if (paths.Any(p => p.Count == depth)) return true;
        if (type is not { IsValueType: true, IsEnum: false } || depth > 6) return false;
        bool any = false;
        foreach (FieldDef field in type.Fields)
        {
            if (field.IsStatic) continue;
            any = true;
            var under = paths.Where(p => p.Count > depth && ReferenceEquals(p[depth], field)).ToList();
            if (under.Count == 0 || !Covers(field.Type.Definition, under, depth + 1)) return false;
        }
        return any;
    }

    private static bool SameType(TypeSig? a, TypeSig? b) =>
        a != null && b != null && (ReferenceEquals(a, b) || (ReferenceEquals(a.Definition, b.Definition) && a.Definition != null && a.ShortName == b.ShortName));

    private static bool IsStruct(TypeSig? type) => type is { IsValueType: true } and not (ByRefSig or PointerSig);

    /// <summary>Whether one of two places in a struct is inside the other (or they are the same place).</summary>
    private static bool Overlap(List<FieldDef> a, List<FieldDef> b)
    {
        for (int i = 0; i < Math.Min(a.Count, b.Count); i++)
            if (!ReferenceEquals(a[i], b[i])) return false;
        return true;
    }

    /// <summary>A value that is worked out without calling anything: nothing a variable could be changed by.</summary>
    private static bool Plain(HExpr e) => HirBuilder.IsPure(e) || (e is HNewObject { Type: { IsValueType: true } } made && made.Arguments.All(Plain));

    /// <summary>Whether a statement can change what a value made of variables comes to.</summary>
    private static bool Changes(HStmt s, HExpr value)
    {
        if (s is not HAssign { Target: var target, Value: var given }) return s is not (HJump or HBranch);
        // (A call may change a variable it was once given the address of; so may a store through a pointer.)
        if (!Plain(given)) return true;
        Path(target, out HExpr root);
        if (root is HLocal { Variable: var variable }) return ConstructorFolding.Mentions(value, variable);
        // (A store into an object or an array changes no variable.)
        return !IsReferenceTarget(root);
    }

    private static bool IsReferenceTarget(HExpr root) => root switch
    {
        HElement => true,
        HField { Object: null } => true,
        _ => root.Type is { IsValueType: false } and not (ByRefSig or PointerSig),
    };

    /// <summary>Whether every statement that names a variable, outside the given ones, only sets it as a whole.</summary>
    private static bool OnlySetElsewhere(HMethod method, HVar variable, Func<HBlock, HStmt, bool> own)
    {
        foreach (HBlock b in method.Blocks)
            foreach (HStmt s in b.Statements)
            {
                if (own(b, s) || !ConstructorFolding.Mentions(s, variable)) continue;
                if (s is HAssign { Target: HLocal { Variable: var set }, Value: var value } && ReferenceEquals(set, variable) && !ConstructorFolding.Mentions(value, variable)) continue;
                return false;
            }
        return true;
    }

    /// <summary>
    /// Whether every use of a variable in an expression reads only parts of it that the given stores set (or does
    /// not read it at all). Its address taken counts as a read of all of it.
    /// </summary>
    private static bool Explained(HExpr? e, HVar x, List<List<FieldDef>> set)
    {
        switch (e)
        {
            case null or HConst or HArg:
                return true;
            case HLocal local:
                return !ReferenceEquals(local.Variable, x) || set.Any(q => q.Count == 0);
            case HField { Object: not null } field when !field.Field.IsStatic:
            {
                List<FieldDef> path = Path(field, out HExpr root);
                if (root is not HLocal { Variable: var owner } || !ReferenceEquals(owner, x)) return Explained(root, x, set);
                if (set.Any(q => q.Count <= path.Count && Overlap(q, path))) return true;
                return Covers(field.Type?.Definition, set.Where(q => q.Count > path.Count && Overlap(q, path)).ToList(), path.Count);
            }
            case HField:
                return true;
            case HElement element:
                return Explained(element.Array, x, set) && Explained(element.Index, x, set);
            case HArrayLength length:
                return Explained(length.Array, x, set);
            case HDeref pointer:
                return Explained(pointer.Pointer, x, set);
            case HUnary unary:
                return Explained(unary.Operand, x, set);
            case HBinary binary:
                return Explained(binary.Left, x, set) && Explained(binary.Right, x, set);
            case HCompare compare:
                return Explained(compare.Left, x, set) && Explained(compare.Right, x, set);
            case HConv conversion:
                return Explained(conversion.Operand, x, set);
            case HCall call:
                return Explained(call.This, x, set) && call.Arguments.All(a => Explained(a, x, set));
            case HNewObject made:
                return made.Arguments.All(a => Explained(a, x, set));
            case HNewArray array:
                return Explained(array.Length, x, set);
            case HTypeExpr typed:
                return Explained(typed.Operand, x, set);
            case HSelect select:
                return Explained(select.Condition, x, set) && Explained(select.WhenTrue, x, set) && Explained(select.WhenFalse, x, set);
            default:
                return !ConstructorFolding.Mentions(e, x);
        }
    }

    private static bool Explained(HStmt s, HVar x, List<List<FieldDef>> set) => s switch
    {
        HAssign a => Explained(a.Target, x, set) && Explained(a.Value, x, set),
        HEval e => Explained(e.Expression, x, set),
        HReturn r => Explained(r.Value, x, set),
        HThrow t => Explained(t.Exception, x, set),
        HBranch b => Explained(b.Condition, x, set),
        HSwitch choice => Explained(choice.Value, x, set),
        _ => true,
    };

    /// <summary>
    /// Whether, going on from the end of a block, the variable can be read before it is set again as a whole
    /// (in one go, or part by part within one block). At the end of <paramref name="head"/> the parts in
    /// <paramref name="there"/> are set as well.
    /// </summary>
    private static bool ReadAfter(HMethod method, HBlock from, HVar x, HBlock head, List<List<FieldDef>> there)
    {
        // (Its address kept anywhere: it can be read without being named.)
        List<List<FieldDef>> all = [[]];
        foreach (HBlock b in method.Blocks)
            foreach (HStmt s in b.Statements)
                if (!Explained(s, x, all))
                    return true;

        var seen = new HashSet<HBlock>();
        var work = new Stack<HBlock>();
        void Enter(HBlock b)
        {
            if (seen.Add(b)) work.Push(b);
        }
        // An exception leads to the handlers of the protected code a block is in, from anywhere in the block.
        void Handlers(int scope)
        {
            for (int s = scope, guard = 0; s >= 0 && guard < 64; guard++, s = method.OuterOf(s))
                if ((s & 1) == 0 && method.TryRegions.TryGetValue(s >> 1, out HTryRegion? region))
                    Enter(region.HandlerEntry);
        }
        if (from.Statements.Count == 0 || from.Statements[^1] is not HJump onward) return true;
        Enter(onward.Target);
        Handlers(from.Scope);
        while (work.Count != 0)
        {
            HBlock b = work.Pop();
            Handlers(b.Scope);
            var set = new List<List<FieldDef>>();
            bool whole = false;
            for (int i = 0; i < b.Statements.Count && !whole; i++)
            {
                HStmt s = b.Statements[i];
                if (ReferenceEquals(b, head) && i == b.Statements.Count - 1)
                {
                    set.AddRange(there);
                    if (Covers(x.Type.Definition, set, 0))
                    {
                        whole = true;
                        break;
                    }
                }
                if (s is HAssign { Target: var target, Value: var value })
                {
                    List<FieldDef> path = Path(target, out HExpr root);
                    if (root is HLocal { Variable: var written } && ReferenceEquals(written, x))
                    {
                        if (!Explained(value, x, set)) return true;
                        set.Add(path);
                        whole = Covers(x.Type.Definition, set, 0);
                        continue;
                    }
                }
                if (!Explained(s, x, set)) return true;
            }
            if (whole || b.Statements.Count == 0) continue;
            switch (b.Statements[^1])
            {
                case HJump jump:
                    Enter(jump.Target);
                    break;
                case HBranch branch:
                    Enter(branch.WhenTrue);
                    Enter(branch.WhenFalse);
                    break;
                case HSwitch choice:
                    foreach (HBlock target in choice.Targets) Enter(target);
                    Enter(choice.Default);
                    break;
            }
        }
        return false;
    }

    /// <summary>
    /// What follows the two paths, where the compiler gave each a copy of its own (the "i++" of the loop both are
    /// in, on the storing path somewhere among its stores): variables set from variables, the same on both and
    /// read by nothing else there. It becomes one block both lead to, so that the paths end where the pasted
    /// method's paths end.
    /// </summary>
    private static void ShareWhatFollows(HMethod method, HBlock direct, HBlock passing)
    {
        List<HStmt> p = passing.Statements, d = direct.Statements;
        if (p.Count < 3 || d.Count < 3 || p[^1] is not HJump after || d[^1] is not HJump other || !ReferenceEquals(after.Target, other.Target)) return;
        int call = p.FindLastIndex(s => s is HEval { Expression: HCall });
        if (call < 0 || call == p.Count - 2) return;
        var following = new List<HAssign>();
        for (int i = call + 1; i < p.Count - 1; i++)
        {
            if (p[i] is not HAssign { Target: HLocal, Value: var value } assign || !Fixed(value)) return;
            following.Add(assign);
        }
        var twins = new List<HStmt>();
        foreach (HAssign assign in following)
        {
            HVar variable = ((HLocal)assign.Target).Variable;
            HStmt? twin = null;
            for (int i = 0; i < d.Count - 1; i++)
            {
                HStmt s = d[i];
                if (s is HAssign { Target: HLocal { Variable: var set }, Value: var value } && ReferenceEquals(set, variable) && HirCleanup.Same(value, assign.Value))
                {
                    if (twin != null) return;
                    twin = s;
                    continue;
                }
                // (The statement moves behind the others there: they are stores of plain values, nothing that calls.)
                if (s is not HAssign { Value: var given } || !Plain(given)) return;
                if (ConstructorFolding.Mentions(s, variable)) return;
                // (Nor does anything on that path set what the statement reads.)
                if (s is HAssign { Target: var target } && Path(target, out HExpr root) is not null && root is HLocal { Variable: var changed } && ConstructorFolding.Mentions(assign.Value, changed)) return;
            }
            if (twin == null) return;
            foreach (HAssign another in following)
                if (!ReferenceEquals(another, assign) && ConstructorFolding.Mentions(another, variable))
                    return;
            twins.Add(twin);
        }
        var join = new HBlock { Id = method.Blocks.Max(b => b.Id) + 1, Scope = passing.Scope };
        foreach (HAssign assign in following)
        {
            p.Remove(assign);
            join.Statements.Add(assign);
        }
        foreach (HStmt twin in twins) d.Remove(twin);
        join.Statements.Add(new HJump(after.Target) { Address = after.Address });
        after.Target = join;
        other.Target = join;
        method.Blocks.Insert(Math.Max(method.Blocks.IndexOf(direct), method.Blocks.IndexOf(passing)) + 1, join);
    }

    private static bool TryJoin(HMethod method, HBlock head, HBranch branch, HBlock direct, HBlock passing, Dictionary<HBlock, int> entries)
    {
        if (ReferenceEquals(direct, head) || ReferenceEquals(passing, head) || direct.Scope != head.Scope || passing.Scope != head.Scope) return false;
        if (entries.GetValueOrDefault(direct) != 1 || entries.GetValueOrDefault(passing) != 1) return false;
        ShareWhatFollows(method, direct, passing);

        // The path that stores the struct: its parts, last, straight into one place - or into a copy of its own
        // that is then stored there whole.
        List<HStmt> d = direct.Statements;
        if (d.Count < 2 || d[^1] is not HJump) return false;
        int last = d.Count - 2;
        HVar? copy = null;
        HElement? place = null;
        if (d[last] is HAssign { Target: HElement into, Value: HLocal { Variable: var staged } } && IsStruct(staged.Type))
        {
            if (!Fixed(into.Array) || !Fixed(into.Index)) return false;
            (copy, place) = (staged, into);
            last--;
        }
        var stored = new List<(List<FieldDef> Path, HExpr Value)>();
        int first = last + 1;
        for (int i = last; i >= 0; i--)
        {
            if (d[i] is not HAssign store) break;
            List<FieldDef> path = Path(store.Target, out HExpr root);
            if (copy != null)
            {
                if (root is not HLocal { Variable: var built } || !ReferenceEquals(built, copy) || ConstructorFolding.Mentions(store.Value, copy)) break;
            }
            else
            {
                if (root is not HElement element || !Fixed(element.Array) || !Fixed(element.Index)) break;
                if (place == null) place = element;
                else if (!HirCleanup.Same(place, element)) break;
            }
            stored.Add((path, store.Value));
            first = i;
        }
        if (stored.Count == 0 || place == null) return false;
        // What that path does before: stores into objects, which change nothing the parts are made of.
        for (int i = 0; i < first; i++)
        {
            if (d[i] is not HAssign { Target: HField { Object: not null } target, Value: var value } || !HirBuilder.IsPure(value)) return false;
            Path(target, out HExpr root);
            if (!IsReferenceTarget(root) || root is HElement) return false;
        }

        // The path that passes it on: parts of it put together, the call, and on.
        List<HStmt> p = passing.Statements;
        if (p.Count < 2 || p[^1] is not HJump || p[^2] is not HEval { Expression: HCall call }) return false;
        HVar? whole = null;
        int handed = 0;
        foreach (HExpr argument in call.Arguments)
            if (argument is HLocal { Variable: var given } && IsStruct(given.Type) && SameType(given.Type, place.Type))
            {
                whole = given;
                handed++;
            }
        if (whole == null || handed != 1 || ReferenceEquals(whole, copy) || ConstructorFolding.Mentions(call.This, whole)) return false;
        foreach (HExpr argument in call.Arguments)
            if (!(argument is HLocal { Variable: var given } && ReferenceEquals(given, whole)) && ConstructorFolding.Mentions(argument, whole))
                return false;
        if (!Covers(whole.Type.Definition, stored.Select(s => s.Path).ToList(), 0)) return false;
        var parts = new List<(List<FieldDef> Path, HAssign Store)>();
        for (int i = 0; i < p.Count - 2; i++)
        {
            if (p[i] is not HAssign store) return false;
            List<FieldDef> path = Path(store.Target, out HExpr root);
            if (root is not HLocal { Variable: var variable } || !ReferenceEquals(variable, whole) || ConstructorFolding.Mentions(store.Value, whole)) return false;
            parts.Add((path, store));
        }

        // Part for part the same: put together on that path, or before the two part (and unchanged since).
        var taken = new bool[parts.Count];
        foreach ((List<FieldDef> path, HExpr value) in stored)
        {
            if (ConstructorFolding.Mentions(value, whole) || (copy != null && ConstructorFolding.Mentions(value, copy))) return false;
            int match = -1;
            for (int k = 0; k < parts.Count && match < 0; k++)
                if (!taken[k] && SamePath(parts[k].Path, path))
                    match = k;
            if (match >= 0)
            {
                if (!Alike(parts[match].Store.Value, value)) return false;
                taken[match] = true;
                continue;
            }
            if (parts.Any(part => Overlap(part.Path, path))) return false;
            HAssign? earlier = null;
            for (int k = head.Statements.Count - 2; k >= 0; k--)
            {
                HStmt s = head.Statements[k];
                if (s is HAssign { Target: var target } before && Path(target, out HExpr root) is { } there && root is HLocal { Variable: var variable } && ReferenceEquals(variable, whole))
                {
                    if (SamePath(there, path)) earlier = before;
                    if (earlier != null || Overlap(there, path)) break;
                    continue;
                }
                // (Anything else that names the struct may have changed it.)
                if (ConstructorFolding.Mentions(s, whole) && s is not HAssign { Target: HLocal }) break;
                if (Changes(s, value)) break;
            }
            if (earlier == null || !Alike(earlier.Value, value)) return false;
        }
        if (taken.Contains(false)) return false;

        // The struct is the method's own copy of what it hands over: nothing else looks at it.
        if (ConstructorFolding.Mentions(branch.Condition, whole) || ConstructorFolding.Mentions(place, whole)) return false;
        for (int i = 0; i < first; i++)
            if (ConstructorFolding.Mentions(d[i], whole))
                return false;
        if (ReadAfter(method, direct, whole, head, parts.Select(part => part.Path).ToList())) return false;
        if (copy != null && !OnlySetElsewhere(method, copy, (b, s) => ReferenceEquals(b, direct) && d.IndexOf(s) >= first)) return false;

        int at = head.Statements.Count - 1;
        foreach ((_, HAssign store) in parts)
        {
            p.Remove(store);
            head.Statements.Insert(at++, store);
        }
        var one = new HAssign(place, new HLocal(whole) { Type = whole.Type }) { Address = d[first].Address };
        d.RemoveRange(first, d.Count - 1 - first);
        d.Insert(first, one);
        return true;
    }
}
