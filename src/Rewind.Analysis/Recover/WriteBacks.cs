using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Removes stores that put back into a struct's field what was read out of that same field.
///
/// A struct taken out of a list and passed on ("var item = list[i]; ... dict[item.slot] = item") is read into
/// registers field by field, and where it is passed on, the registers are written into the stack memory it is
/// passed in - which may be the memory it was read from. Translated, that is "item.f = t" after "t = item.f":
/// the same value written back, which changes nothing. Where the field cannot be written by the source (it is
/// readonly, or the storage of a property), C# refuses the store. It is removed where nothing can have changed
/// the struct in between: no statement on the way writes it, a part of it, or hands out its address.
/// </summary>
internal static class WriteBacks
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_WRITE_BACKS") != null;

    private static bool IsStruct(TypeSig? t) => t is { IsValueType: true } and not (PrimitiveSig or PointerSig or ByRefSig or OpaqueSig) && t.Definition is { IsEnum: false };

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

    public static void Run(HMethod method, ProgramAnalysis program)
    {
        if (Disabled) return;
        // Variables given a value once, and those given the value of a field of a struct variable (read as the
        // field, or through the property it is the storage of).
        var assignments = new Dictionary<HVar, int>();
        var reads = new Dictionary<HVar, (HBlock Block, int Index, HVar Struct, FieldDef? Field, MethodDef? Getter)>();
        foreach (HBlock block in method.Blocks)
            for (int i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not HAssign { Target: HLocal { Variable: var t }, Value: var value }) continue;
                assignments[t] = assignments.GetValueOrDefault(t) + 1;
                if (value is HField { Object: HLocal { Variable: var s } owner, Field: { IsStatic: false } f } && IsStruct(owner.Type))
                    reads[t] = (block, i, s, f, null);
                else if (value is HCall { This: var on, Arguments.Length: 0, Method: { IsStatic: false } getter } &&
                         (on is HAddressOf { Target: var inner } ? inner : on) is HLocal { Variable: var gs } gowner && IsStruct(gowner.Type) &&
                         getter.Name.StartsWith("get_", StringComparison.Ordinal))
                    reads[t] = (block, i, gs, null, getter);
            }
        bool ReadOf((HBlock, int, HVar, FieldDef? Field, MethodDef? Getter) read, FieldDef f) =>
            read.Field != null ? ReferenceEquals(read.Field, f)
                : read.Getter != null && ReferenceEquals(read.Getter.DeclaringType, f.DeclaringType) &&
                  (AccessorIndex.AutoPropertyName(f) is { } name ? read.Getter.Name == "get_" + name : ReferenceEquals(program.Accessors.GetterOf(f), read.Getter));
        if (reads.Count == 0) return;

        var removed = new List<(HBlock Block, HStmt Statement)>();
        foreach (HBlock block in method.Blocks)
            for (int j = 0; j < block.Statements.Count; j++)
            {
                if (block.Statements[j] is not HAssign { Target: HField { Object: HLocal { Variable: var s }, Field: var f }, Value: HLocal { Variable: var t } } store) continue;
                if (!Unwritable(f) || assignments.GetValueOrDefault(t) != 1 || !reads.TryGetValue(t, out var read)) continue;
                if (!ReferenceEquals(read.Struct, s) || !ReadOf(read, f)) continue;
                if (!Unchanged(method, s, f, read.Block, read.Index, block, j)) continue;
                removed.Add((block, store));
            }
        foreach (var (block, statement) in removed) block.Statements.Remove(statement);
    }

    /// <summary>A field the source cannot write outside a constructor: readonly, or the storage of a property.</summary>
    private static bool Unwritable(FieldDef f) => !f.IsStatic && ((f.Attrs & FieldDef.InitOnly) != 0 || AccessorIndex.IsBackingField(f));

    /// <summary>
    /// No statement between the read and the store, on any way from one to the other, changes the variable. (A way
    /// that comes back to the read reads again: from there it is that read the store puts back.)
    /// </summary>
    private static bool Unchanged(HMethod method, HVar v, FieldDef field, HBlock from, int after, HBlock to, int before)
    {
        if (ReferenceEquals(from, to) && after < before)
            return Range(from.Statements, after + 1, before).All(s => !Changes(s, v, field));
        // The blocks on a way from the read to the store that does not pass the read again.
        var forward = new HashSet<HBlock>();
        var work = new Stack<HBlock>(Successors(from));
        while (work.Count > 0)
        {
            HBlock b = work.Pop();
            if (ReferenceEquals(b, from)) continue;
            if (forward.Count > 256) return false;
            if (forward.Add(b)) foreach (HBlock next in Successors(b)) work.Push(next);
        }
        if (!forward.Contains(to)) return false;
        var predecessors = new Dictionary<HBlock, List<HBlock>>();
        foreach (HBlock b in method.Blocks)
            foreach (HBlock next in Successors(b))
            {
                if (!predecessors.TryGetValue(next, out List<HBlock>? list)) predecessors[next] = list = [];
                list.Add(b);
            }
        var between = new HashSet<HBlock>();
        work.Push(to);
        while (work.Count > 0)
        {
            HBlock b = work.Pop();
            if (!between.Add(b)) continue;
            if (predecessors.TryGetValue(b, out List<HBlock>? list))
                foreach (HBlock p in list)
                    if (forward.Contains(p))
                        work.Push(p);
        }
        // The store's block, where a way comes round to it again without the read: whole (what follows the store
        // there comes before it the next time).
        bool cycles = false;
        var again = new HashSet<HBlock>();
        var loop = new Stack<HBlock>(Successors(to));
        while (loop.Count > 0 && !cycles)
        {
            HBlock b = loop.Pop();
            if (ReferenceEquals(b, from)) continue;
            if (ReferenceEquals(b, to) || again.Count > 256) cycles = true;
            else if (again.Add(b)) foreach (HBlock next in Successors(b)) loop.Push(next);
        }
        if (Range(from.Statements, after + 1, from.Statements.Count).Any(s => Changes(s, v, field))) return false;
        foreach (HBlock b in between)
        {
            IEnumerable<HStmt> statements = ReferenceEquals(b, to) && !cycles ? Range(b.Statements, 0, before) : b.Statements;
            if (statements.Any(s => Changes(s, v, field))) return false;
        }
        return true;
    }

    private static IEnumerable<HStmt> Range(List<HStmt> statements, int start, int end)
    {
        for (int i = Math.Max(0, start); i < end && i < statements.Count; i++) yield return statements[i];
    }

    private static bool Rooted(HExpr e, HVar v)
    {
        while (true)
            switch (e)
            {
                case HLocal l: return ReferenceEquals(l.Variable, v);
                case HField { Object: { } o }: e = o; continue;
                default: return false;
            }
    }

    /// <summary>The statement writes the variable or a part of it, takes its address, or calls something on it that may change it.</summary>
    /// <summary>The field of the variable a place is in (null: the variable itself).</summary>
    private static FieldDef? FirstField(HExpr e, HVar v)
    {
        FieldDef? first = null;
        while (e is HField { Object: { } o } f)
        {
            first = f.Field;
            e = o;
        }
        return first;
    }

    private static bool Changes(HStmt s, HVar v, FieldDef field)
    {
        // (Another field of it written changes nothing of this one.)
        if (s is HAssign { Target: var target } && Rooted(target, v) && FirstField(target, v) is var first && (first == null || ReferenceEquals(first, field))) return true;
        // (A variable whose address is taken may be written through it, where no statement names it.)
        if (v.AddressTaken && s is HAssign { Target: HDeref }) return true;
        bool changes = false;
        FinallyFolding.Visit(s, e =>
        {
            switch (e)
            {
                case HAddressOf a when Rooted(a.Target, v):
                    changes = true;
                    break;
                // (A property read of the struct changes nothing; any other method of it may.)
                case HCall { This: { } on, Method: var m } when Rooted(on is HAddressOf { Target: var inner } ? inner : on, v) &&
                                                               !(m.Name.StartsWith("get_", StringComparison.Ordinal) && m.Parameters.Length == 0):
                    changes = true;
                    break;
            }
        });
        return changes;
    }
}
