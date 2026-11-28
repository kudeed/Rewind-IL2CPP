using Rewind.Analysis.Hir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts constructors back from what they leave: every field of a struct (or of an object just allocated) set.
///
/// Where the C++ compiler pasted a constructor in, it also moved its work around: the checks of the arguments
/// ("name ?? string.Empty") go where the values are worked out, the stores go where the struct is wanted - into
/// the field of another object, or into the copy handed to a call - and a struct passed whole is copied field by
/// field from where it came from. Compared statement by statement with the constructor, nothing lines up. What
/// does: the value each field ends up with. For a run of stores that sets every field the constructor sets, each
/// field's value is compared with what the constructor stores there, worked out from its parameters - and where
/// one set of arguments gives them all, the run is "s = new S(arguments)".
///
/// A run that sets every field of a struct to the same field of one other struct is a copy of that struct.
/// </summary>
internal static class StructFromParts
{
    private static readonly bool Disabled = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_FROM_PARTS") != null;

    private sealed record Coalesced(HExpr Value, HExpr Otherwise);

    public static bool Run(HMethod method, MethodPipeline pipeline)
    {
        if (Disabled) return false;
        // Copies made of a struct's fields just stored: made of the values stored.
        bool forwarded = FieldForwarding.Run(method);
        bool any = false;
        for (int round = 0; round < 32; round++)
        {
            var defs = Definitions.Of(method);
            bool changed = false;
            foreach (HBlock block in method.Blocks)
            {
                for (int i = 0; i < block.Statements.Count && !changed; i++)
                    changed = TryRun(method, block, i, defs, pipeline);
                if (changed) break;
            }
            if (!changed) break;
            any = true;
        }
        // What was stored only to be read back by a copy now made of the values is stored for nothing.
        if (forwarded || any) DeadStores.Run(method);
        return any || forwarded;
    }

    // ---- what variables hold -------------------------------------------------------------------------------

    /// <summary>The assignments of each variable, and the blocks leading into each block.</summary>
    private sealed class Definitions
    {
        public Dictionary<HVar, List<(HBlock Block, int Index, HExpr Value)>> Assigned = [];
        public Dictionary<HBlock, List<HBlock>> Predecessors = [];

        public static Definitions Of(HMethod method)
        {
            var d = new Definitions();
            foreach (HBlock block in method.Blocks)
            {
                for (int i = 0; i < block.Statements.Count; i++)
                    if (block.Statements[i] is HAssign { Target: HLocal { Variable: var v }, Value: var value })
                    {
                        if (!d.Assigned.TryGetValue(v, out var list)) d.Assigned[v] = list = [];
                        list.Add((block, i, value));
                    }
                foreach (HBlock next in Successors(block))
                {
                    if (!d.Predecessors.TryGetValue(next, out var list)) d.Predecessors[next] = list = [];
                    list.Add(block);
                }
            }
            return d;
        }

        /// <summary>
        /// "x ?? otherwise": a variable given x on the way where x is not null, and something else on the other -
        /// the two ways out of one test of x.
        /// </summary>
        public Coalesced? CoalescedIn(HVar v)
        {
            if (!Assigned.TryGetValue(v, out var list) || list.Count != 2) return null;
            foreach (var (a, b) in new[] { (list[0], list[1]), (list[1], list[0]) })
            {
                HBlock? test = Test(a.Block, b.Block);
                if (test?.Statements[^1] is not HBranch { Condition: HCompare { Op: HCompareOp.Ne or HCompareOp.Eq } c } branch) continue;
                HExpr? tested = c.Right is HConst { Value: null } ? c.Left : c.Left is HConst { Value: null } ? c.Right : null;
                if (tested == null || !Equal(tested, a.Value)) continue;
                // The way the value is not null leads to its assignment.
                HBlock whenSet = c.Op == HCompareOp.Ne ? branch.WhenTrue : branch.WhenFalse;
                if (!Leads(whenSet, a.Block)) continue;
                // (What it is otherwise may be made just before: "o = new List(); m = o".)
                HExpr otherwise = b.Value;
                if (otherwise is HLocal { Variable: var held } && Assigned.TryGetValue(held, out var made) && made.Count == 1 &&
                    made[0].Value is HNewObject or HConst or HField { Object: null }) otherwise = made[0].Value;
                return new Coalesced(a.Value, otherwise);
            }
            return null;
        }

        /// <summary>The block whose test the two blocks come from (each reached only from it, possibly through a jump).</summary>
        private HBlock? Test(HBlock a, HBlock b)
        {
            HBlock? From(HBlock x)
            {
                for (int hops = 0; hops < 4; hops++)
                {
                    if (!Predecessors.TryGetValue(x, out var p) || p.Count != 1) return null;
                    if (p[0].Statements.Count != 0 && p[0].Statements[^1] is HBranch) return p[0];
                    x = p[0];
                }
                return null;
            }
            HBlock? ta = From(a), tb = From(b);
            return ta != null && ReferenceEquals(ta, tb) ? ta : null;
        }

        private static bool Leads(HBlock from, HBlock to)
        {
            for (int hops = 0; hops < 4; hops++)
            {
                if (ReferenceEquals(from, to)) return true;
                if (from.Statements.Count == 0 || from.Statements[^1] is not HJump j) return false;
                from = j.Target;
            }
            return false;
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

    /// <summary>What a value is, looked through variables given one value once, conversions and "?? otherwise".</summary>
    private static object Meaning(HExpr e, Definitions defs, int depth = 0)
    {
        while (e is HConv c) e = c.Operand;
        if (depth > 8 || e is not HLocal { Variable: var v }) return e;
        if (defs.CoalescedIn(v) is { } coalesced) return coalesced;
        if (defs.Assigned.TryGetValue(v, out var list) && list.Count == 1 && Stable(list[0].Value)) return Meaning(list[0].Value, defs, depth + 1);
        return e;
    }

    /// <summary>A value that is the same wherever it is worked out: constants, variables, arguments, and reads of fields and properties of those.</summary>
    private static bool Stable(HExpr e) => e switch
    {
        HConst or HLocal or HArg => true,
        HConv c => Stable(c.Operand),
        HField f => f.Object == null ? f.Field.Name == "Empty" : Stable(f.Object),
        HCall { Arguments.Length: 0, This: { } on, Method: { Name: var name, IsStatic: false } } => name.StartsWith("get_", StringComparison.Ordinal) && Stable(on),
        HCall { Arguments.Length: 0, This: null, Method: { Name: "get_Empty" or "get_zero" or "get_one" } } => true,
        _ => false,
    };

    /// <summary>Structural equality, with property reads compared like field reads.</summary>
    internal static bool Equal(HExpr? a, HExpr? b)
    {
        while (a is HConv ca) a = ca.Operand;
        while (b is HConv cb) b = cb.Operand;
        if (ReferenceEquals(a, b)) return true;
        if (a == null || b == null) return false;
        switch (a, b)
        {
            case (HConst x, HConst y):
                return Equals(x.Value, y.Value) || Integral(x.Value) is { } i && Integral(y.Value) is { } j && i == j;
            case (HCall x, HCall y):
                return ReferenceEquals(x.Method, y.Method) && Equal(x.This, y.This) && x.Arguments.Length == y.Arguments.Length &&
                       x.Arguments.Zip(y.Arguments).All(p => Equal(p.First, p.Second)) && (x.Method.Name.StartsWith("get_", StringComparison.Ordinal) || x.Arguments.Length == 0);
            case (HNewObject x, HNewObject y):
                return ReferenceEquals(x.Constructor, y.Constructor) && x.Arguments.Length == y.Arguments.Length && x.Arguments.Zip(y.Arguments).All(p => Equal(p.First, p.Second));
            case (HField x, HField y):
                return ReferenceEquals(x.Field, y.Field) && Equal(x.Object, y.Object);
            case (HCompare x, HCompare y):
                return x.Op == y.Op && Equal(x.Left, y.Left) && Equal(x.Right, y.Right);
            case (HBinary x, HBinary y):
                return x.Op == y.Op && Equal(x.Left, y.Left) && Equal(x.Right, y.Right);
            default:
                return HirCleanup.Same(a, b);
        }
    }

    private static long? Integral(object? v) => v switch
    {
        bool b => b ? 1 : 0,
        int i => i,
        long l => l,
        byte b => b,
        sbyte s => s,
        short s => s,
        ushort u => u,
        uint u => u,
        _ => null,
    };

    // ---- the runs ------------------------------------------------------------------------------------------

    private static bool IsStruct(TypeSig? t) => t is { IsValueType: true } and not (PrimitiveSig or PointerSig or ByRefSig or OpaqueSig) && t.Definition is { IsEnum: false };

    private static bool OnlyConstructors(FieldDef f) => (f.Attrs & FieldDef.InitOnly) != 0 || AccessorIndex.IsBackingField(f);

    /// <summary>The run of stores into the fields of one struct place starting at the statement, if it sets every field.</summary>
    private static bool TryRun(HMethod method, HBlock block, int i, Definitions defs, MethodPipeline pipeline)
    {
        if (block.Statements[i] is not HAssign { Target: HField { Object: { } place } first }) return false;
        // The start of the run: the statement before writes something else.
        if (i > 0 && block.Statements[i - 1] is HAssign { Target: HField { Object: { } before } } && Equal(before, place)) return false;
        TypeSig? type = place.Type;
        bool isObject = false;
        (HBlock Block, int Index)? allocation = null, baseCall = null;
        if (!IsStruct(type))
        {
            // An object allocated raw before (here, or on the way here), its base constructor run.
            if (place is not HLocal { Variable: var o } || type?.Definition is not { IsValueType: false } klass || klass.GenericParameters.Length != 0) return false;
            bool Scan(HBlock b, int from)
            {
                for (int k = from; k >= 0; k--)
                {
                    HStmt s = b.Statements[k];
                    if (s is HAssign { Target: HLocal { Variable: var made }, Value: HTypeExpr { Op: HTypeOp.Allocate } } && ReferenceEquals(made, o)) { allocation = (b, k); return true; }
                    if (s is HEval { Expression: HCall { Method.Name: ".ctor", This: HLocal { Variable: var on } } } && ReferenceEquals(on, o))
                    {
                        if (baseCall != null) return false;
                        baseCall = (b, k);
                        continue;
                    }
                    if (ConstructorFolding.Mentions(s, o)) return false;
                }
                return true;
            }
            if (!Scan(block, i - 1)) return false;
            if (allocation == null)
            {
                // The ways back to the allocation, none of which does anything with the object.
                var seen = new HashSet<HBlock> { block };
                var work = new Queue<HBlock>();
                foreach (HBlock p in defs.Predecessors.GetValueOrDefault(block, [])) work.Enqueue(p);
                if (work.Count == 0) return false;
                while (work.Count > 0)
                {
                    HBlock b = work.Dequeue();
                    if (!seen.Add(b)) continue;
                    if (seen.Count > 8) return false;
                    if (!Scan(b, b.Statements.Count - 1)) return false;
                    if (allocation != null && ReferenceEquals(allocation.Value.Block, b)) continue; // (not past it)
                    var leading = defs.Predecessors.GetValueOrDefault(b, []);
                    if (leading.Count == 0) return false;
                    foreach (HBlock p in leading) work.Enqueue(p);
                }
            }
            if (allocation == null) return false;
            isObject = true;
        }
        TypeDef definition = type!.Definition!;
        if (!OnlyConstructors(first.Field) || !ReferenceEquals(first.Field.DeclaringType, definition)) return false;

        var values = new Dictionary<FieldDef, HExpr>();
        var readAt = new Dictionary<FieldDef, int>();
        int end = i;
        while (end < block.Statements.Count && block.Statements[end] is HAssign { Target: HField { Object: { } owner } target, Value: var value } &&
               Equal(owner, place) && ReferenceEquals(target.Field.DeclaringType, definition) && !target.Field.IsStatic)
        {
            if (!values.TryAdd(target.Field, value)) return false;
            readAt[target.Field] = end;
            end++;
        }
        var fields = definition.Fields.Where(f => !f.IsStatic).ToList();
        if (fields.Count == 0 || !isObject && values.Count != fields.Count) return false;
        // (Values that read what the run writes are left alone.)
        foreach (HExpr v in values.Values)
            if (!isObject && Mentions(v, place)) return false;

        // A copy of one struct, read field by field.
        if (!isObject && HirBuilder.IsPure(place) && CopyOf(values, readAt, fields, defs, type, block, i) is { } source)
        {
            Replace(block, i, end, new HAssign(place, source) { Address = block.Statements[end - 1].Address });
            return true;
        }

        // An exact whole-value copy also works for a constructed generic type. Constructor recovery needs
        // instantiated signatures and bodies; leave that separate limitation in place.
        if (type is GenericInstSig || definition.GenericParameters.Length != 0) return false;

        foreach (MethodDef constructor in definition.Methods)
        {
            if (constructor.Name != ".ctor" || constructor.IsStatic || constructor.Address == 0) continue;
            if (ReferenceEquals(constructor, method.Method)) continue;
            if (pipeline.CoreBody(constructor) is not { } body || FieldsSet(body) is not { } set) continue;
            if (set.Fields.Count != values.Count || !set.Fields.Keys.All(values.ContainsKey)) continue;
            if (isObject != set.BaseCall) continue;
            if (Arguments(constructor, set.Fields, values, defs, place) is not { } arguments) continue;
            var made = new HNewObject { Constructor = constructor, Arguments = arguments, Type = type };
            if (isObject)
            {
                // The object made at the end of the run; its allocation and its base constructor's call go.
                HExpr target = place;
                Replace(block, i, end, new HAssign(target, made) { Address = block.Statements[end - 1].Address });
                // (The later of the two first, where they are in one block.)
                var (allocBlock, allocIndex) = allocation!.Value;
                if (baseCall is var (callBlock, callIndex))
                {
                    if (ReferenceEquals(callBlock, allocBlock) && callIndex < allocIndex) allocIndex--;
                    callBlock.Statements.RemoveAt(callIndex);
                }
                allocBlock.Statements.RemoveAt(allocIndex);
                method.Notes.Remove($"the constructor of {type.ShortName} was inlined here; the object is allocated raw and its statements follow");
            }
            else Replace(block, i, end, new HAssign(place, made) { Address = block.Statements[end - 1].Address });
            return true;
        }
        return false;
    }

    private static void Replace(HBlock block, int start, int end, HStmt with)
    {
        block.Statements.RemoveRange(start, end - start);
        block.Statements.Insert(start, with);
    }

    private static bool Mentions(HExpr e, HExpr place)
    {
        bool found = false;
        FinallyFolding.Visit(e, x => found |= Equal(x, place));
        return found;
    }

    /// <summary>
    /// The struct every field was read from, only when reading it at the replacement still gives those values.
    /// Meaning deliberately ignores where values were computed; a copy cannot: a saved field may predate a
    /// clear of the source, a call through an alias, or a write to the saved local itself.
    /// </summary>
    private static HExpr? CopyOf(Dictionary<FieldDef, HExpr> values, Dictionary<FieldDef, int> readAt,
        List<FieldDef> fields, Definitions defs, TypeSig type, HBlock block, int copyAt)
    {
        HExpr? source = null;
        foreach (FieldDef f in fields)
        {
            HExpr? meaning = CopyMeaning(values[f], defs, block, readAt[f], copyAt);
            HExpr? from = meaning is HField read && ReferenceEquals(read.Field, f) ? read.Object : null;
            if (from == null || from.Type?.Key != type.Key) return null;
            if (source == null) source = from;
            else if (!Equal(source, from)) return null;
        }
        return source != null && HirBuilder.IsPure(source) ? source : null;
    }

    private static HExpr? CopyMeaning(HExpr value, Definitions defs, HBlock block, int useAt, int copyAt, int depth = 0)
    {
        if (depth > 8) return null;
        // A conversion that changes the value cannot disappear in a whole-struct assignment.
        while (value is HConv conversion)
        {
            if (conversion.Type == null || conversion.Type.Key != conversion.Operand.Type?.Key || !HirBuilder.IsPure(conversion)) return null;
            value = conversion.Operand;
        }
        if (value is HLocal { Variable: var local })
        {
            if (local.AddressTaken || !defs.Assigned.TryGetValue(local, out var assigned) || assigned.Count != 1) return null;
            var definition = assigned[0];
            // Same-block dominance only. A definition in a predecessor can belong to a different iteration
            // or exception path; proving that case needs more than a global count of assignments.
            if (!ReferenceEquals(definition.Block, block) || definition.Index >= useAt || definition.Index >= copyAt) return null;
            if (!StructFolding.Movable(value, block.Statements, definition.Index, useAt - 1, null) ||
                !StructFolding.Movable(definition.Value, block.Statements, definition.Index, copyAt - 1, null)) return null;
            return CopyMeaning(definition.Value, defs, block, definition.Index, copyAt, depth + 1);
        }
        // Reads in later stores move to the first store; saved reads move forward from their definition.
        // In either direction all intervening writes and calls must preserve the value. Calls/getters
        // themselves are not accepted merely because their names look like properties.
        return value is HField && StructFolding.Movable(value, block.Statements,
            Math.Min(useAt, copyAt) - 1, Math.Max(useAt, copyAt) - 1, null) ? value : null;
    }

    private sealed record SetFields(Dictionary<FieldDef, object> Fields, bool BaseCall);

    /// <summary>What a constructor stores in each field of its object, in terms of its parameters.</summary>
    private static SetFields? FieldsSet(HMethod body)
    {
        var defs = Definitions.Of(body);
        var set = new Dictionary<FieldDef, object>();
        bool baseCall = false;
        foreach (HBlock block in body.Blocks)
            foreach (HStmt s in block.Statements)
                switch (s)
                {
                    case HAssign { Target: HField { Object: HArg { Index: -1 }, Field: var f }, Value: var value }:
                        if (!set.TryAdd(f, Meaning(value, defs))) return null;
                        break;
                    case HAssign { Target: HLocal }:
                    case HJump or HBranch or HReturn { Value: null }:
                        break;
                    case HEval { Expression: HCall { Method.Name: ".ctor", This: HArg { Index: -1 }, Arguments.Length: 0 } }:
                        baseCall = true;
                        break;
                    default:
                        return null; // does something else as well
                }
        return new SetFields(set, baseCall);
    }

    /// <summary>The arguments that make the constructor store what the run stores, or null.</summary>
    private static HExpr[]? Arguments(MethodDef constructor, Dictionary<FieldDef, object> stores, Dictionary<FieldDef, HExpr> values, Definitions defs, HExpr place)
    {
        var arguments = new HExpr?[constructor.Parameters.Length];
        var later = new List<(object Expected, HExpr Value)>();
        foreach (var (field, expected) in stores)
        {
            HExpr value = values[field];
            object meaning = Meaning(value, defs);
            switch (expected)
            {
                case HArg { Index: >= 0 and var k } when k < arguments.Length:
                    if (!Bind(arguments, k, value)) return null;
                    break;
                case Coalesced { Value: HArg { Index: >= 0 and var k } } c when k < arguments.Length:
                    // "parameter ?? otherwise": the place has "x ?? otherwise" (x is the argument), or a value never null.
                    if (meaning is Coalesced had && Equal(had.Otherwise, c.Otherwise)) { if (!Bind(arguments, k, had.Value)) return null; }
                    else if (NeverNull(meaning)) { if (!Bind(arguments, k, value)) return null; }
                    else return null;
                    break;
                case HConst constant:
                    if (meaning is not HExpr given || !Equal(constant, given)) return null;
                    break;
                case HExpr other:
                    later.Add((other, value));
                    break;
                default:
                    return null;
            }
        }
        if (arguments.Any(a => a == null)) return null;
        // What the constructor works out of its arguments and its own fields: the same here.
        foreach (var (expected, value) in later)
        {
            HExpr substituted = Substitute((HExpr)expected, arguments!, place);
            if (!Equal(substituted, Meaning(value, defs) as HExpr ?? value) && !Equal(substituted, value)) return null;
        }
        return arguments!;
    }

    private static bool Bind(HExpr?[] arguments, int k, HExpr value)
    {
        while (value is HConv c && c.Operand.Type is { } inner && inner.Key == value.Type?.Key) value = c.Operand;
        if (arguments[k] == null) { arguments[k] = value; return true; }
        return Equal(arguments[k], value);
    }

    private static bool NeverNull(object meaning) => meaning switch
    {
        HConst { Value: string } => true,
        HNewObject or HNewArray => true,
        HField { Object: null, Field.Name: "Empty" } => true,
        _ => false,
    };

    private static HExpr Substitute(HExpr e, HExpr[] arguments, HExpr place) => EnumeratorLoops.Rewrite(HirCopy.Of(e), x => x switch
    {
        HArg { Index: -1 } => HirCopy.Of(place),
        HArg { Index: >= 0 and var k } when k < arguments.Length => HirCopy.Of(arguments[k]),
        _ => null,
    });
}
