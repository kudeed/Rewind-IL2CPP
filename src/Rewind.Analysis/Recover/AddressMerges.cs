using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Removes variables that only ever hold the address of one local.
///
/// Where two paths meet, the machine code has "the address of the bounds" in a register on both - handed back
/// by the call that filled them on each path - and what follows reads through that register. Translated
/// literally that is a reference variable given the same address in two places: correct, but not something
/// C# lets one write (a reference to a local cannot be put into a variable declared before it), and not what
/// was written - the code after the two paths simply uses the local.
///
/// A variable whose every assignment gives it the address of the same place inside a local (the local itself,
/// or a field of a struct held in it) is replaced by that address wherever it is read. The address of a local
/// is the same wherever it is taken, so it does not matter which assignment a read follows.
/// </summary>
internal static class AddressMerges
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_ADDRESS_MERGES") != null;

    private static bool IsStruct(TypeSig? t) => t is { IsValueType: true } and not (PrimitiveSig or PointerSig or ByRefSig or OpaqueSig) && t.Definition is { IsEnum: false };

    /// <summary>The variable a place lies in: the place itself, or a chain of fields of structs held in it.</summary>
    private static HVar? RootOf(HExpr place)
    {
        HExpr e = place;
        while (e is HField { Object: { } owner } field && !field.Field.IsStatic && IsStruct(owner.Type)) e = owner;
        return e is HLocal l ? l.Variable : null;
    }

    /// <summary>Whether an expression mentions a variable.</summary>
    private static bool Names(HExpr e, HVar variable)
    {
        bool found = false;
        FinallyFolding.Visit(e, x => found |= x is HLocal l && ReferenceEquals(l.Variable, variable));
        return found;
    }

    private static HExpr Clone(HExpr place) => place switch
    {
        HLocal l => new HLocal(l.Variable) { Type = l.Type },
        HField f => new HField { Object = Clone(f.Object!), Field = f.Field, DeclaringType = f.DeclaringType, Type = f.Type },
        _ => place,
    };

    public static bool Run(HMethod method)
    {
        if (Disabled || method.Blocks.Count == 0) return false;
        bool merged = SamePlace(method);
        if (!NoChosenValues && ChosenValues(method)) merged = true;
        if (!NoSplitUses && SplitUses(method)) merged = true;
        return merged;
    }

    private static readonly bool NoSplitUses = Environment.GetEnvironmentVariable("REWIND_NO_SPLIT_USES") != null;

    /// <summary>
    /// A reference variable given a different place on each path and used in the first statement where the
    /// paths meet - handed to a call ("f(n, ref *p)"), stored through. The source had that statement on each
    /// path, with the place written out ("if (c) f(0, ref a); else f(1, ref b);"), and the compiler made one
    /// statement of the two. It goes back to the end of each path, with that path's place in it.
    /// </summary>
    private static bool SplitUses(HMethod method)
    {
        var given = new Dictionary<HVar, List<(HBlock Block, HAssign Statement, HExpr Place)>?>();
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
            {
                if (s is not HAssign { Target: HLocal { Variable: var variable } } assignment || variable.Type is not ByRefSig) continue;
                if (given.TryGetValue(variable, out var known) && known == null) continue;
                if (assignment.Value is HAddressOf { Target: var target } && !Names(target, variable) && HirBuilder.IsPure(target) &&
                    (known == null || known.All(p => !ReferenceEquals(p.Block, block))))
                {
                    if (known == null) given[variable] = known = [];
                    known.Add((block, assignment, target));
                }
                else given[variable] = null;
            }
        foreach (HTryRegion region in method.TryRegions.Values) given.Remove(region.Exception);
        if (!given.Values.Any(places => places is { Count: >= 2 })) return false;

        var predecessors = new Dictionary<HBlock, List<HBlock>>();
        foreach (HBlock block in method.Blocks)
        {
            if (block.Statements.Count == 0) continue;
            IEnumerable<HBlock> next = block.Statements[^1] switch
            {
                HJump j => [j.Target],
                HBranch b => [b.WhenTrue, b.WhenFalse],
                HSwitch sw => [.. sw.Targets, sw.Default],
                _ => [],
            };
            foreach (HBlock target in next)
            {
                if (!predecessors.TryGetValue(target, out List<HBlock>? list)) predecessors[target] = list = [];
                if (!list.Contains(block)) list.Add(block);
            }
        }

        bool any = false;
        foreach (var (variable, places) in given.ToList())
        {
            if (places is not { Count: >= 2 } || variable.AddressTaken) continue;
            // The paths end with the address taken (and at most plain values set after it), and meet in one block
            // that nothing else leads to.
            if (places[0].Block.Statements[^1] is not HJump { Target: var join } || join.Statements.Count == 0) continue;
            if (method.TryRegions.Values.Any(r => ReferenceEquals(r.Entry, join) || ReferenceEquals(r.HandlerEntry, join))) continue;
            if (!predecessors.TryGetValue(join, out List<HBlock>? into) || into.Count != places.Count || places.Any(p => !into.Contains(p.Block))) continue;
            bool fits = true;
            foreach (var (block, statement, place) in places)
            {
                if (block.Scope != join.Scope || block.Statements[^1] is not HJump { Target: var next } || !ReferenceEquals(next, join)) fits = false;
                for (int k = block.Statements.IndexOf(statement) + 1; fits && k < block.Statements.Count - 1; k++)
                    fits = block.Statements[k] is HAssign { Target: HLocal { Variable: var set }, Value: var value } && HirBuilder.IsPure(value) &&
                           set.Type is not (ByRefSig or PointerSig) && !ReferenceEquals(set, variable) && !Names(place, set);
            }
            if (!fits) continue;
            // Every use is in the first statement there.
            HStmt use = join.Statements[0];
            if (use is not (HAssign or HEval)) continue;
            int elsewhere = 0, here = 0;
            foreach (HBlock block in method.Blocks)
                foreach (HStmt s in block.Statements)
                    FinallyFolding.Visit(s, e =>
                    {
                        if (e is not HLocal l || !ReferenceEquals(l.Variable, variable)) return;
                        if (ReferenceEquals(s, use)) here++;
                        else elsewhere++;
                    });
            if (here == 0 || elsewhere != places.Count) continue;

            foreach (var (block, statement, place) in places)
            {
                HExpr? Map(HExpr e)
                {
                    switch (e)
                    {
                        case HAddressOf { Target: HDeref { Pointer: HLocal l } } when ReferenceEquals(l.Variable, variable):
                            return new HAddressOf(HirCopy.Of(place)) { Type = e.Type };
                        case HDeref { Pointer: HLocal l } when ReferenceEquals(l.Variable, variable):
                            return HirCopy.Of(place);
                        case HField { Object: HLocal l } f when ReferenceEquals(l.Variable, variable):
                            return new HField { Object = HirCopy.Of(place), Field = f.Field, DeclaringType = f.DeclaringType, Type = f.Type };
                        case HLocal l when ReferenceEquals(l.Variable, variable):
                            return new HAddressOf(HirCopy.Of(place)) { Type = e.Type };
                        default:
                            return null;
                    }
                }
                block.Statements.Insert(block.Statements.Count - 1, HirCopy.Of(use, Map)!);
                block.Statements.Remove(statement);
            }
            join.Statements.RemoveAt(0);
            any = true;
        }
        return any;
    }

    private static readonly bool NoChosenValues = Environment.GetEnvironmentVariable("REWIND_NO_CHOSEN_VALUES") != null;

    /// <summary>
    /// A variable given the address of one local on one path and of another on the next, and then only read
    /// through: "p = &amp;a" here, "p = &amp;b" there, "x = *p" after. The source chose between two values
    /// ("x = c ? a : b"); the machine code chooses between their addresses, the values being too big for a
    /// register. A reference variable set after it is declared is not something C# lets one write. Where
    /// nothing touches the locals once their address is taken, choosing the value does the same: "v = a" here,
    /// "v = b" there, "x = v" after.
    /// </summary>
    private static bool ChosenValues(HMethod method)
    {
        // What each reference variable is given: addresses of places, and nothing else.
        var given = new Dictionary<HVar, List<(HBlock Block, HAssign Statement, HExpr Place, HVar? Root)>?>();
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
            {
                if (s is not HAssign { Target: HLocal { Variable: var variable } } assignment || variable.Type is not ByRefSig) continue;
                if (given.TryGetValue(variable, out var known) && known == null) continue;
                if (assignment.Value is HAddressOf { Target: var target } && target.Type != null && ((ByRefSig)variable.Type).ElementType.Key == target.Type.Key &&
                    !Names(target, variable))
                {
                    HVar? root = RootOf(target);
                    if (root != null && root.Type is ByRefSig or PointerSig) root = null;
                    if (known == null) given[variable] = known = [];
                    known.Add((block, assignment, target, root));
                }
                else given[variable] = null;
            }
        foreach (HTryRegion region in method.TryRegions.Values) given.Remove(region.Exception);
        var chosen = new HashSet<HVar>();
        foreach (var (variable, places) in given)
            if (places is { Count: >= 2 } && !variable.AddressTaken && places.Any(p => !HirCleanup.Same(p.Place, places[0].Place)))
                chosen.Add(variable);
        if (chosen.Count == 0) return false;

        // Read through, and nothing else: every mention is the pointer of a read, or the assignment itself.
        var mentions = new Dictionary<HVar, int>();
        var reads = new Dictionary<HVar, int>();
        var where = new Dictionary<HVar, List<(HBlock Block, int Index)>>();
        var readAt = new Dictionary<HVar, List<(HBlock Block, int Index)>>();
        foreach (HBlock block in method.Blocks)
            for (int i = 0; i < block.Statements.Count; i++)
            {
                HStmt s = block.Statements[i];
                if (s is HAssign { Target: var written })
                {
                    HExpr e = written;
                    while (e is HField { Object: { } owner }) e = owner;
                    if (e is HDeref { Pointer: HLocal { Variable: var through } }) chosen.Remove(through);
                    if (e is HLocal { Variable: var whole } && !ReferenceEquals(e, written)) chosen.Remove(whole);
                }
                int at = i;
                void Read(HVar v)
                {
                    reads[v] = reads.GetValueOrDefault(v) + 1;
                    if (!readAt.TryGetValue(v, out var read)) readAt[v] = read = [];
                    read.Add((block, at));
                }
                FinallyFolding.Visit(s, e =>
                {
                    switch (e)
                    {
                        case HLocal { Variable: var v }:
                            mentions[v] = mentions.GetValueOrDefault(v) + 1;
                            if (!where.TryGetValue(v, out var list)) where[v] = list = [];
                            list.Add((block, at));
                            break;
                        case HDeref { Pointer: HLocal { Variable: var v } }:
                            Read(v);
                            break;
                        // (A field of what a reference variable leads to.)
                        case HField { Object: HLocal { Variable: { Type: ByRefSig } v } }:
                            Read(v);
                            break;
                    }
                });
            }
        chosen.RemoveWhere(v => mentions.GetValueOrDefault(v) != reads.GetValueOrDefault(v) + given[v]!.Count);

        // What is read through the variable later must be what the place held when its address was taken. A
        // local that is not named again after that holds it. Any other place does where nothing is done in
        // between: the address is the last thing taken before the paths meet, and where they meet nothing is
        // called or stored before the reads.
        bool Quiet(HVar v)
        {
            if (!readAt.TryGetValue(v, out var read) || read.Count == 0) return false;
            HBlock join = read[0].Block;
            if (read.Any(r => !ReferenceEquals(r.Block, join))) return false;
            foreach (var (block, statement, _, _) in given[v]!)
            {
                int taken = block.Statements.IndexOf(statement);
                if (taken != block.Statements.Count - 2 || block.Statements[^1] is not HJump { Target: var next } || !ReferenceEquals(next, join)) return false;
            }
            int last = read.Max(r => r.Index);
            // (Places that are all in locals: a field of an object or an array element stored in between is
            // other memory - the struct read through the variable being copied field by field, say.)
            bool locals = given[v]!.All(p => p.Root != null);
            for (int k = 0; k < last; k++)
            {
                if (join.Statements[k] is not HAssign { Target: var target, Value: var value } || !HirBuilder.IsPure(value)) return false;
                HExpr e = target;
                while (e is HField { Object: { } owner } f && !f.Field.IsStatic && IsStruct(owner.Type)) e = owner;
                if (e is HLocal { Variable: var set })
                {
                    if (set.Type is ByRefSig or PointerSig || ReferenceEquals(set, v)) return false;
                    if (given[v]!.Any(p => ReferenceEquals(p.Root, set) || Names(p.Place, set))) return false;
                }
                else if (!locals || e is not (HField or HElement)) return false;
            }
            return true;
        }
        chosen.RemoveWhere(v => !Quiet(v) && given[v]!.Any(p =>
        {
            if (p.Root == null) return true;
            int taken = p.Block.Statements.IndexOf(p.Statement);
            return where[p.Root].Any(m => !ReferenceEquals(m.Block, p.Block) || m.Index > taken);
        }));
        if (chosen.Count == 0) return false;

        foreach (HVar variable in chosen)
        {
            variable.Type = ((ByRefSig)variable.Type).ElementType;
            foreach (var (_, assignment, place, _) in given[variable]!)
            {
                assignment.Target = new HLocal(variable) { Type = variable.Type };
                assignment.Value = place;
            }
        }
        HExpr? Map(HExpr e)
        {
            if (e is HDeref { Pointer: HLocal { Variable: var through } } && chosen.Contains(through)) return new HLocal(through) { Type = through.Type };
            if (e is HLocal { Variable: var named } local && chosen.Contains(named)) local.Type = named.Type;
            return null;
        }
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                EnumeratorLoops.Rewrite(s, Map);
        return true;
    }

    private static bool SamePlace(HMethod method)
    {
        // What each variable is given: the one place whose address it always is, or null for anything else.
        var places = new Dictionary<HVar, HExpr?>();
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
            {
                if (s is not HAssign { Target: HLocal { Variable: var variable } } assignment) continue;
                if (places.TryGetValue(variable, out HExpr? known) && known == null) continue;
                HExpr? place = assignment.Value is HAddressOf { Target: var target } && RootOf(target) is { } root && !ReferenceEquals(root, variable) ? target : null;
                places[variable] = place != null && (known == null || HirCleanup.Same(known, place)) ? known ?? place : null;
            }
        foreach (HTryRegion region in method.TryRegions.Values) places.Remove(region.Exception);
        var chosen = new Dictionary<HVar, HExpr>();
        foreach (var (variable, place) in places)
            if (place != null && !variable.AddressTaken && variable.Type is ByRefSig or PointerSig)
                chosen[variable] = place;
        if (chosen.Count == 0) return false;
        // A variable used in any other way than read (its own address taken, say) stays.
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                FinallyFolding.Visit(s, e =>
                {
                    if (e is HAddressOf { Target: HLocal { Variable: var taken } }) chosen.Remove(taken);
                });
        if (chosen.Count == 0) return false;

        HExpr? Map(HExpr e)
        {
            switch (e)
            {
                case HDeref { Pointer: HLocal { Variable: var through } } when chosen.TryGetValue(through, out HExpr? place):
                    return Clone(place);
                case HField { Object: HLocal { Variable: var owner } } field when chosen.TryGetValue(owner, out HExpr? place):
                    return new HField { Object = Clone(place), Field = field.Field, DeclaringType = field.DeclaringType, Type = field.Type };
                case HLocal { Variable: var read } local when chosen.TryGetValue(read, out HExpr? place):
                    return new HAddressOf(Clone(place)) { Type = local.Type };
                default:
                    return null;
            }
        }

        foreach (HBlock block in method.Blocks)
        {
            block.Statements.RemoveAll(s => s is HAssign { Target: HLocal { Variable: var given } } && chosen.ContainsKey(given));
            foreach (HStmt s in block.Statements) EnumeratorLoops.Rewrite(s, Map);
        }
        return true;
    }
}
