using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Reads of a field of a struct variable that was just given a value there, read as that value.
///
/// The C++ compiler keeps a struct it is making in stack memory it uses for other things as well, and copies
/// it on field by field ("issue.code = 3; ...; copy.code = issue.code"). With each read of a field that only
/// constructors write (readonly, or the storage of a property) put as the value stored before it - on every
/// way there, with nothing in between changing the field or that value - the copy is made of the values
/// themselves, and the stores into the first struct are left for nothing (DeadStores removes them).
/// </summary>
internal static class FieldForwarding
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_FIELD_FORWARDING") != null;

    private static bool IsStruct(TypeSig? t) => t is { IsValueType: true } and not (PrimitiveSig or PointerSig or ByRefSig or OpaqueSig) && t.Definition is { IsEnum: false };

    private static bool OnlyConstructors(FieldDef f) => !f.IsStatic && ((f.Attrs & FieldDef.InitOnly) != 0 || AccessorIndex.IsBackingField(f));

    private static bool Forwardable(HExpr v) => v is HConst or HLocal || v is HField { Object: null, Field.Name: "Empty" };

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

    [ThreadStatic] private static HashSet<HVar>? _escaped;

    private sealed class Known : Dictionary<(HVar Variable, FieldDef Field), HExpr>
    {
        public Known() { }
        public Known(Known other) : base(other) { }
    }

    public static bool Run(HMethod method)
    {
        if (Disabled || method.Blocks.Count == 0) return false;
        // Only blocks of the method's own code: nothing is carried into or out of a handler.
        var predecessors = new Dictionary<HBlock, List<HBlock>>();
        foreach (HBlock b in method.Blocks)
            foreach (HBlock next in Successors(b))
            {
                if (!predecessors.TryGetValue(next, out var list)) predecessors[next] = list = [];
                list.Add(b);
            }
        var handlers = new HashSet<HBlock>(method.TryRegions.Values.Select(r => r.HandlerEntry));
        // The variables whose address the method hands out somewhere: a call may change those.
        _escaped = [];
        foreach (HBlock b in method.Blocks)
            foreach (HStmt s in b.Statements)
                FinallyFolding.Visit(s, e =>
                {
                    if (e is not HAddressOf a) return;
                    HExpr root = a.Target;
                    while (root is HField { Object: { } o }) root = o;
                    if (root is HLocal { Variable: var v }) _escaped.Add(v);
                });
        var entry = new Dictionary<HBlock, Known?>();
        foreach (HBlock b in method.Blocks) entry[b] = null; // not reached yet: anything
        entry[method.Blocks[0]] = new Known();
        foreach (HBlock h in handlers) entry[h] = new Known();
        bool changed = true;
        for (int round = 0; changed && round < 16; round++)
        {
            changed = false;
            foreach (HBlock b in method.Blocks)
            {
                if (ReferenceEquals(b, method.Blocks[0]) || handlers.Contains(b)) continue;
                Known? met = null;
                foreach (HBlock p in predecessors.GetValueOrDefault(b, []))
                {
                    if (entry[p] is not { } before) continue;
                    Known after = Through(p, before, null);
                    met = met == null ? after : Meet(met, after);
                }
                met ??= new Known();
                if (entry[b] is not { } old || !Same(old, met))
                {
                    entry[b] = met;
                    changed = true;
                }
            }
        }
        if (changed) return false; // did not settle: leave everything as it is
        bool any = false;
        foreach (HBlock b in method.Blocks)
            if (entry[b] is { } state)
                Through(b, state, () => any = true);
        return any;
    }

    private static Known Meet(Known a, Known b)
    {
        var met = new Known();
        foreach (var (key, value) in a)
            if (b.TryGetValue(key, out HExpr? other) && StructFromParts.Equal(value, other))
                met[key] = value;
        return met;
    }

    private static bool Same(Known a, Known b) => a.Count == b.Count && a.All(kv => b.TryGetValue(kv.Key, out HExpr? v) && StructFromParts.Equal(v, kv.Value));

    /// <summary>The state after the block; with <paramref name="replaced"/> set, its reads are put as what is known.</summary>
    private static Known Through(HBlock block, Known start, Action? replaced)
    {
        var state = new Known(start);
        foreach (HStmt s in block.Statements)
        {
            if (replaced != null && state.Count != 0) Replace(s, state, replaced);
            Apply(s, state);
        }
        return state;
    }

    /// <summary>The field of a struct variable a read reads: "x.f", or "x.get_P()" of the property f is the storage of.</summary>
    private static (HVar, FieldDef)? ReadOf(HExpr e)
    {
        switch (e)
        {
            case HField { Object: HLocal { Variable: var x } local, Field: var f } when IsStruct(local.Type) && OnlyConstructors(f):
                return (x, f);
            case HCall { This: var on, Arguments.Length: 0, Method: { IsStatic: false, Name: var name } getter } when name.StartsWith("get_", StringComparison.Ordinal):
            {
                if ((on is HAddressOf { Target: var inner } ? inner : on) is not HLocal { Variable: var x } local || !IsStruct(local.Type)) return null;
                string property = name[4..];
                FieldDef? f = getter.DeclaringType.Fields.FirstOrDefault(field => !field.IsStatic && AccessorIndex.AutoPropertyName(field) == property);
                return f != null && ReferenceEquals(local.Type!.Definition, getter.DeclaringType) ? (x, f) : null;
            }
            default:
                return null;
        }
    }

    private static void Replace(HStmt s, Known state, Action replaced)
    {
        HExpr Map(HExpr e) => EnumeratorLoops.Rewrite(e, x => ReadOf(x) is { } key && state.TryGetValue(key, out HExpr? value) ? Replaced(value) : null);
        HExpr Replaced(HExpr value)
        {
            replaced();
            return HirCopy.Of(value);
        }
        switch (s)
        {
            case HAssign a:
                a.Value = Map(a.Value);
                // (The place written: only what it is reached through is read.)
                if (a.Target is HElement el) { el.Array = Map(el.Array); el.Index = Map(el.Index); }
                break;
            case HEval e: e.Expression = Map(e.Expression); break;
            case HReturn { Value: { } } r: r.Value = Map(r.Value!); break;
            case HBranch b: b.Condition = Map(b.Condition); break;
            case HSwitch sw: sw.Value = Map(sw.Value); break;
        }
    }

    private static void Apply(HStmt s, Known state)
    {
        if (state.Count == 0 && s is not HAssign) return;
        // What changes a variable, or a value known.
        void Forget(HVar v) { foreach (var key in state.Keys.Where(k => ReferenceEquals(k.Variable, v)).ToList()) state.Remove(key); }
        void ForgetValuesOf(HVar v) { foreach (var key in state.Where(kv => ConstructorFolding.Mentions(kv.Value, v)).Select(kv => kv.Key).ToList()) state.Remove(key); }
        bool calls = false;
        FinallyFolding.Visit(s, e =>
        {
            switch (e)
            {
                case HAddressOf a:
                {
                    HExpr root = a.Target;
                    while (root is HField { Object: { } o }) root = o;
                    if (root is HLocal { Variable: var v }) Forget(v);
                    break;
                }
                case HCall c when !(c.Method.Name.StartsWith("get_", StringComparison.Ordinal) && c.Arguments.Length == 0):
                {
                    calls = true;
                    HExpr? on = c.This is HAddressOf { Target: var inner } ? inner : c.This;
                    while (on is HField { Object: { } o }) on = o;
                    if (on is HLocal { Variable: var v }) Forget(v);
                    break;
                }
            }
        });
        // (A call may reach a variable whose address was handed out before.)
        if (calls) foreach (var key in state.Keys.Where(k => _escaped!.Contains(k.Variable)).ToList()) state.Remove(key);
        if (s is not HAssign { Target: var target, Value: var value }) return;
        switch (target)
        {
            case HLocal { Variable: var v }:
                Forget(v);
                ForgetValuesOf(v);
                break;
            case HField { Object: HLocal { Variable: var x } local, Field: var f } when IsStruct(local.Type):
                if (OnlyConstructors(f) && Forwardable(value) && !(value is HLocal { Variable: var self } && ReferenceEquals(self, x))) state[(x, f)] = value;
                else state.Remove((x, f));
                break;
            default:
            {
                HExpr root = target;
                FieldDef? first = null;
                while (root is HField { Object: { } o } part)
                {
                    first = part.Field;
                    root = o;
                }
                if (root is HLocal { Variable: var v })
                {
                    if (first == null) Forget(v);
                    else state.Remove((v, first));
                }
                break;
            }
        }
    }
}
