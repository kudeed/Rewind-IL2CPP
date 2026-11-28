using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// A complete struct read into registers before its storage is changed: take the value whole at the first
/// read, then read the existing temporaries from that snapshot. Later struct folding can put the saved parts
/// together without exposing the fields or rereading storage which has since been cleared.
/// </summary>
internal static class StructSnapshots
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_SNAPSHOTS") != null;
    private const int Window = 64;
    private sealed record Read(HAssign Assignment, HField[] Path);

    public static bool Run(HMethod method, LayoutCalculator layouts)
    {
        if (Disabled) return false;
        bool any = false;
        foreach (HBlock block in method.Blocks)
            for (int first = 0; first < block.Statements.Count; first++)
            {
                if (block.Statements[first] is not HAssign { Target: HLocal, Value: HField field }) continue;
                bool changed = false;
                // The largest completely read value first: an awaiter, not just the task inside it.
                foreach (HExpr owner in Owners(field).Reverse())
                {
                    if (!NamedPlace(owner) || !HirBuilder.IsPure(owner) || ReadBefore(owner, block.Statements, first) ||
                        !ValidTree(owner.Type!, layouts, 0)) continue;
                    var reads = new List<Read>();
                    int last = first;
                    for (; last < block.Statements.Count && last - first < Window; last++)
                    {
                        // One straight-line read window. Unknown calls, stores through aliases, and control
                        // flow stay in place and end the search; no effects are moved past the snapshot.
                        if (block.Statements[last] is not HAssign { Target: HLocal, Value: var value } assignment || !HirBuilder.IsPure(value)) break;
                        if (value is HField part && Path(part, owner) is { Length: > 0 } path) reads.Add(new Read(assignment, path));
                        if (reads.Count < 2 || !Covers(owner.Type!, reads.Select(r => r.Path).ToArray(), layouts, 0)) continue;
                        if (!StructFolding.Movable(owner, block.Statements, first - 1, last, null)) break;
                        // A saved copy is useful when the original really changes. This also prevents later
                        // passes from repeatedly taking a snapshot of the untouched snapshot local.
                        if (!ChangedLater(owner, block.Statements, last + 1)) break;
                        HVar snapshot = method.NewLocal(owner.Type!, "snapshot");
                        foreach (Read read in reads)
                        {
                            HExpr from = new HLocal(snapshot) { Type = snapshot.Type };
                            foreach (HField step in read.Path)
                                from = new HField { Object = from, Field = step.Field, DeclaringType = step.DeclaringType, Type = step.Type };
                            read.Assignment.Value = from;
                        }
                        block.Statements.Insert(first, new HAssign(new HLocal(snapshot) { Type = snapshot.Type }, HirCopy.Of(owner))
                            { Address = block.Statements[first].Address });
                        any = true;
                        changed = true;
                        first = last + 1;
                        break;
                    }
                    if (changed) break;
                }
            }
        return any;
    }

    private static bool Struct(TypeSig? type) => type is { IsValueType: true, ContainsGenericParameter: false } and not
        (PrimitiveSig or ByRefSig or PointerSig or OpaqueSig) && type.Definition is { IsEnum: false, IsByRefLike: false } definition &&
        (definition.GenericParameters.Length == 0 || type is GenericInstSig instance && instance.Arguments.Length == definition.GenericParameters.Length);

    private static IEnumerable<HExpr> Owners(HField read)
    {
        for (HExpr? owner = read.Object; owner != null; owner = owner is HField field ? field.Object : null)
        {
            if (!Struct(owner.Type)) yield break;
            yield return owner;
        }
    }

    private static bool NamedPlace(HExpr owner) => owner switch
    {
        HLocal or HArg => owner.Type is not (ByRefSig or PointerSig),
        HField { Object: { } parent, Field.IsStatic: false } => NamedPlace(parent),
        _ => false,
    };

    private static bool Same(HExpr left, HExpr right) => left.Type != null && left.Type.Key == right.Type?.Key && HirCleanup.Same(left, right);

    private static HField[]? Path(HField read, HExpr owner)
    {
        var reverse = new List<HField>();
        HExpr current = read;
        for (int depth = 0; depth < 9; depth++)
        {
            if (Same(current, owner))
            {
                reverse.Reverse();
                return [.. reverse];
            }
            if (current is not HField { Object: { } parent, Field.IsStatic: false } field) return null;
            reverse.Add(field);
            current = parent;
        }
        return null;
    }

    private static bool Within(HExpr place, HExpr owner)
    {
        for (int depth = 0; depth < 10; depth++)
        {
            if (Same(place, owner)) return true;
            if (place is not HField { Object: { } parent, Field.IsStatic: false }) return false;
            place = parent;
        }
        return false;
    }

    private static bool ChangedLater(HExpr owner, List<HStmt> statements, int start)
    {
        for (int i = start; i < statements.Count && i - start < Window; i++)
            if (statements[i] is HAssign { Target: var target } && (Within(target, owner) || Within(owner, target))) return true;
        return false;
    }

    private static bool ReadBefore(HExpr owner, List<HStmt> statements, int start)
    {
        // Start at the first read of this source in a pure run. In particular, do not reinterpret a suffix
        // of a run containing duplicate/overlapping reads as a second independent complete copy.
        for (int i = start - 1; i >= 0 && start - i <= Window; i--)
        {
            if (statements[i] is not HAssign { Target: HLocal, Value: var value } || !HirBuilder.IsPure(value)) break;
            if (value is HField field && Path(field, owner) != null) return true;
        }
        return false;
    }

    private static FieldSlot[]? Fields(TypeSig type, LayoutCalculator layouts)
    {
        if (!Struct(type)) return null;
        TypeLayout layout = layouts.Of(type);
        FieldSlot[] fields = layout.Fields.OrderBy(f => f.Offset).ToArray();
        if (!layout.Known || layout.Size <= 0 || fields.Length == 0 || fields.Length > Window ||
            fields.Length != type.Definition!.Fields.Count(f => !f.IsStatic)) return null;
        int end = 0;
        foreach (FieldSlot field in fields)
        {
            if (field.Field.IsStatic || !ReferenceEquals(field.Field.DeclaringType, type.Definition) || field.Size <= 0 ||
                field.Offset < end || field.Offset + field.Size > layout.Size || field.Type.ContainsGenericParameter || field.Type is OpaqueSig or ByRefSig) return null;
            end = field.Offset + field.Size;
        }
        return fields;
    }

    private static bool ValidTree(TypeSig type, LayoutCalculator layouts, int depth)
    {
        if (depth > 8 || Fields(type, layouts) is not { } fields) return false;
        foreach (FieldSlot field in fields)
            if (field.Type.Definition is { IsValueType: true, IsEnum: false } && field.Type is not PrimitiveSig &&
                !ValidTree(field.Type, layouts, depth + 1)) return false;
        return true;
    }

    private static bool Covers(TypeSig type, HField[][] paths, LayoutCalculator layouts, int depth)
    {
        if (depth > 8 || paths.Length == 0 || Fields(type, layouts) is not { } fields) return false;
        if (paths.Any(path => path.Length == 0)) return paths.Length == 1;
        foreach (HField[] path in paths)
        {
            HField first = path[0];
            int at = Array.FindIndex(fields, f => ReferenceEquals(f.Field, first.Field));
            if (at < 0 || first.Object?.Type?.Key != type.Key || first.Type?.Key != fields[at].Type.Key ||
                first.DeclaringType != null && first.DeclaringType.Key != type.Key) return false;
        }
        foreach (FieldSlot field in fields)
        {
            HField[][] under = paths.Where(path => ReferenceEquals(path[0].Field, field.Field)).Select(path => path[1..]).ToArray();
            if (under.Length == 0) return false;
            // A complete substruct read covers its entire subtree; repeated or parent/child reads do not
            // establish a one-to-one copy and are conservatively left alone.
            if (under.Any(path => path.Length == 0))
            {
                if (under.Length != 1) return false;
            }
            else if (!Covers(field.Type, under, layouts, depth + 1)) return false;
        }
        return true;
    }
}
