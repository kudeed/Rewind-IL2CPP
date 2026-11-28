using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text.Json;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

// Small semantic regressions at the HIR materialization/folding boundary. No native lift, SDK
// implementation, or game-method substitution is involved. Existing Rewind binaries are referenced.
internal static class Program
{
    private const BindingFlags All = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
    private static readonly Assembly Analysis = typeof(HirBuilder).Assembly;
    private static readonly Type SemType = Analysis.GetType("Rewind.Analysis.Recover.Sem", true)!;
    private static readonly Type PartsType = Analysis.GetType("Rewind.Analysis.Recover.SParts", true)!;
    private static readonly Type PartType = Analysis.GetType("Rewind.Analysis.Recover.Part", true)!;
    private static readonly Type ValueType = Analysis.GetType("Rewind.Analysis.Recover.SVal", true)!;
    private static readonly Type Folding = Analysis.GetType("Rewind.Analysis.Recover.StructFromParts", true)!;
    private static readonly Type Definitions = Folding.GetNestedType("Definitions", BindingFlags.NonPublic)!;
    private static readonly Type Snapshots = Analysis.GetType("Rewind.Analysis.Recover.StructSnapshots", true)!;
    private static readonly SigFactory Signatures = new();
    private static readonly PrimitiveSig Object = Primitive(Il2CppTypeEnum.Object);
    private static readonly PrimitiveSig String = Primitive(Il2CppTypeEnum.String);
    private static readonly PrimitiveSig Int = Primitive(Il2CppTypeEnum.I4);
    private static readonly PrimitiveSig Short = Primitive(Il2CppTypeEnum.I2);
    private static readonly PrimitiveSig Bool = Primitive(Il2CppTypeEnum.Boolean);
    private static int assertions;
    private static int definitionIndex;
    private static readonly List<object> Cases = [];

    private static void Check(bool condition, string message)
    {
        assertions++;
        if (!condition) throw new InvalidOperationException(message);
    }

    private static T Key<T>(T type, string key) where T : TypeSig
    {
        typeof(TypeSig).GetProperty(nameof(TypeSig.Key))!.SetValue(type, key);
        return type;
    }

    private static PrimitiveSig Primitive(Il2CppTypeEnum element) => Key(new PrimitiveSig(element, null), "p:" + element);

    private static TypeDef Define(string name, bool valueType, params (string Name, TypeSig Type)[] fields)
    {
        var definition = new TypeDef { Index = ++definitionIndex, Name = name, IsValueType = valueType, Assembly = new AssemblyModel { Name = "SnapshotFixture" } };
        definition.Sig = Key(new TypeDefSig(definition), name);
        definition.Fields = fields.Select((field, index) => new FieldDef {
            Name = field.Name, Type = field.Type, Index = index, DeclaringType = definition,
            Attrs = FieldDef.InitOnly | 1
        }).ToArray();
        return definition;
    }

    private static HField Field(HExpr owner, FieldDef field, TypeSig? type = null) =>
        new() { Object = owner, Field = field, DeclaringType = owner.Type, Type = type ?? field.Type };
    private static HLocal Local(HVar variable) => new(variable) { Type = variable.Type };
    private static HTypeExpr Zero(TypeSig type) => new(HTypeOp.Default, type, null) { Type = type };

    private sealed record Fixture(HMethod Method, HBlock Block, TypeDef Struct, HExpr Source, HLocal Destination, HArg State);

    private static Fixture FixtureOf(TypeDef structure, TypeSig? instance = null)
    {
        TypeSig type = instance ?? structure.Sig;
        var state = Define("State" + type.Key, false, ("awaiter", type), ("unrelated", Int));
        var method = new HMethod { Method = new MethodDef { Name = "MoveNext", DeclaringType = state } };
        var block = new HBlock();
        method.Blocks.Add(block);
        var self = new HArg(-1) { Type = state.Sig };
        return new Fixture(method, block, structure, Field(self, state.Fields[0]), Local(method.NewLocal(type)), self);
    }

    private static bool Fold(Fixture fixture, int at)
    {
        object definitions = Definitions.GetMethod("Of", All)!.Invoke(null, [fixture.Method])!;
        // Fixtures have no constructors. A null pipeline proves the copy path needs no native body lookup.
        return (bool)Folding.GetMethod("TryRun", All)!.Invoke(null, [fixture.Method, fixture.Block, at, definitions, null])!;
    }

    private static List<HExpr> ReadFields(Fixture fixture)
    {
        var held = new List<HExpr>();
        foreach (var field in fixture.Struct.Fields)
        {
            HLocal local = Local(fixture.Method.NewLocal(field.Type));
            fixture.Block.Statements.Add(new HAssign(local, Field(fixture.Source, field)));
            held.Add(local);
        }
        return held;
    }

    private static int WriteFields(Fixture fixture, IReadOnlyList<HExpr> values)
    {
        int at = fixture.Block.Statements.Count;
        for (int i = 0; i < fixture.Struct.Fields.Length; i++)
            fixture.Block.Statements.Add(new HAssign(Field(fixture.Destination, fixture.Struct.Fields[i]), values[i]));
        return at;
    }

    private static HirBuilder Materializer(HMethod method, HBlock block)
    {
        var builder = (HirBuilder)RuntimeHelpers.GetUninitializedObject(typeof(HirBuilder));
        // Only the computed-value boundary is exercised, not ELF/model discovery. Initialize its normal
        // collection fields, then provide the real HIR method/block used by Emit and NewLocal.
        foreach (var field in typeof(HirBuilder).GetFields(All).Where(f => !f.IsStatic))
        {
            Type type = field.FieldType;
            if (type.IsGenericType && type.GetGenericTypeDefinition() is var generic &&
                (generic == typeof(Dictionary<,>) || generic == typeof(HashSet<>) || generic == typeof(List<>)))
                field.SetValue(builder, Activator.CreateInstance(type));
        }
        typeof(HirBuilder).GetField("_h", All)!.SetValue(builder, method);
        typeof(HirBuilder).GetField("_cur", All)!.SetValue(builder, block);
        return builder;
    }

    private static object Materialize(HirBuilder builder, Node node, object value)
    {
        var boundary = typeof(HirBuilder).GetMethod("Materialize", All, null, [typeof(Node), SemType, typeof(bool)], null)!;
        boundary.Invoke(builder, [node, value, false]);
        var meanings = (IDictionary)typeof(HirBuilder).GetField("_sem", All)!.GetValue(builder)!;
        return meanings[node]!;
    }

    private static object Parts(IEnumerable<(int Offset, int Size, HExpr Value)> fields, int size)
    {
        var list = (IList)Activator.CreateInstance(typeof(List<>).MakeGenericType(PartType))!;
        foreach (var field in fields) list.Add(Activator.CreateInstance(PartType, field.Offset, field.Size, field.Value)!);
        return Activator.CreateInstance(PartsType, list, size)!;
    }

    private static HExpr[] PartValues(object parts) =>
        ((IEnumerable)PartsType.GetField("Parts")!.GetValue(parts)!).Cast<object>()
        .Select(part => (HExpr)PartType.GetProperty("Value")!.GetValue(part)!).ToArray();

    private static void SnapshotCase(string name, int width, (string Name, TypeSig Type, int Offset, int Size, object? Value)[] layout)
    {
        var structure = Define(name, true, layout.Select(f => (f.Name, f.Type)).ToArray());
        var fixture = FixtureOf(structure);
        var builder = Materializer(fixture.Method, fixture.Block);
        var values = new HExpr[layout.Length];
        for (int word = 0; word < width; word += 8)
        {
            int at = word;
            int[] indexes = Enumerable.Range(0, layout.Length).Where(i => layout[i].Offset >= at && layout[i].Offset < at + 8).ToArray();
            if (indexes.Length == 0) continue;
            var node = new Node { Id = word, Op = Op.Load, Type = VT.I64, Addr = (ulong)(0x1000 + word) };
            if (indexes.Length == 1 && layout[indexes[0]].Size == 8)
            {
                int index = indexes[0];
                object value = Activator.CreateInstance(ValueType, Field(fixture.Source, structure.Fields[index]))!;
                values[index] = (HExpr)ValueType.GetField("Expr")!.GetValue(Materialize(builder, node, value))!;
            }
            else
            {
                object input = Parts(indexes.Select(i => (layout[i].Offset - word, layout[i].Size,
                    (HExpr)Field(fixture.Source, structure.Fields[i]))), 8);
                object output = Materialize(builder, node, input);
                Check((int)PartsType.GetField("Size")!.GetValue(output)! == 8, name + " keeps the word width including padding");
                var outputParts = ((IEnumerable)PartsType.GetField("Parts")!.GetValue(output)!).Cast<object>().ToArray();
                var held = PartValues(output);
                for (int i = 0; i < indexes.Length; i++)
                {
                    int index = indexes[i];
                    values[index] = held[i];
                    Check(held[i] is HLocal && ReferenceEquals(held[i].Type, layout[index].Type), name + " captures the typed field");
                    Check((int)PartType.GetProperty("Offset")!.GetValue(outputParts[i])! == layout[index].Offset - word &&
                        (int)PartType.GetProperty("Size")!.GetValue(outputParts[i])! == layout[index].Size, name + " preserves leaf range");
                }
            }
        }
        fixture.Block.Statements.Add(new HAssign(fixture.Source, Zero(fixture.Source.Type!)));
        int writeAt = WriteFields(fixture, values);
        Check(!Fold(fixture, writeAt), name + " cannot reread the cleared source");
        var machine = new Machine(fixture, layout.Select(v => v.Value).ToArray());
        machine.Run();
        for (int i = 0; i < layout.Length; i++)
            Check(Equals(machine.Destination[structure.Fields[i]], layout[i].Value), name + " retains " + layout[i].Name);
        Check(machine.Source.Values.All(v => v is null || Equals(v, 0) || Equals(v, (short)0) || Equals(v, false)), name + " still clears the stored awaiter");
        Cases.Add(new { name, bytes = width, result = "load snapshot survives clear; every field preserved" });
    }

    private static void CopyCases()
    {
        TypeDef pair = Define("Pair", true, ("source", Object), ("token", Short));
        Fixture Fresh() => FixtureOf(pair);
        void Reject(string name, Action<Fixture, List<HExpr>> change)
        {
            Fixture fixture = Fresh();
            var values = ReadFields(fixture);
            change(fixture, values);
            int at = WriteFields(fixture, values);
            Check(!Fold(fixture, at), name);
            Cases.Add(new { name, result = "conservative rejection" });
        }
        var untouched = Fresh();
        int untouchedAt = WriteFields(untouched, ReadFields(untouched));
        Check(Fold(untouched, untouchedAt), "unchanged saved fields become a whole copy");

        var unrelated = Fresh();
        var unrelatedValues = ReadFields(unrelated);
        unrelated.Block.Statements.Add(new HAssign(Field(unrelated.State, unrelated.State.Type!.Definition!.Fields[1]), new HConst(3, Int)));
        Check(Fold(unrelated, WriteFields(unrelated, unrelatedValues)), "a proved unrelated write does not disable copies");

        Reject("source cleared between load and copy", (f, _) => f.Block.Statements.Add(new HAssign(f.Source, Zero(f.Source.Type!))));
        Reject("one source field changed", (f, _) => f.Block.Statements.Add(new HAssign(Field(f.Source, pair.Fields[1]), new HConst((short)0, Short))));
        Reject("unknown call may change object storage", (f, _) => f.Block.Statements.Add(new HEval(new HCall {
            Method = new MethodDef { Name = "Unknown", DeclaringType = pair }, This = f.State })));
        Reject("saved scalar passed by reference", (_, values) => ((HLocal)values[1]).Variable.AddressTaken = true);
        Reject("write through a possibly aliasing pointer", (f, _) => f.Block.Statements.Add(new HAssign(
            new HDeref(new HArg(0) { Type = new ByRefSig(pair.Sig) }) { Type = pair.Sig }, Zero(pair.Sig))));
        Reject("conversion cannot disappear", (_, values) => values[1] = new HConv(HConvKind.U1, values[1]) { Type = Primitive(Il2CppTypeEnum.U1) });

        var cross = Fresh();
        var crossValues = ReadFields(cross);
        var predecessor = cross.Block;
        var next = new HBlock { Id = 1 };
        cross.Method.Blocks.Add(next);
        cross = cross with { Block = next };
        predecessor.Statements.Add(new HJump(next));
        Check(!Fold(cross, WriteFields(cross, crossValues)), "a predecessor assignment is not assumed to dominate");

        var forward = Fresh();
        var forwardValues = ReadFields(forward);
        var assignments = forward.Block.Statements.ToArray();
        forward.Block.Statements.Clear();
        int forwardAt = WriteFields(forward, forwardValues);
        forward.Block.Statements.AddRange(assignments);
        Check(!Fold(forward, forwardAt), "a definition after use cannot be followed");

        var getter = Fresh();
        var getterMethod = new MethodDef { Name = "get_Source", DeclaringType = pair, ReturnType = pair.Sig };
        var getterValues = pair.Fields.Select(field => (HExpr)Field(new HCall { Method = getterMethod, Type = pair.Sig }, field)).ToArray();
        Check(!Fold(getter, WriteFields(getter, getterValues)), "a getter is not assumed pure from its name");
        var counter = new Machine(getter, [new object(), (short)42]);
        counter.Run();
        Check(counter.Calls == 2, "getter evaluation count is preserved");

        var targetGetter = Fresh();
        var targetMethod = new MethodDef { Name = "get_Destination", DeclaringType = pair, ReturnType = pair.Sig };
        int targetAt = targetGetter.Block.Statements.Count;
        foreach (var field in pair.Fields) targetGetter.Block.Statements.Add(new HAssign(
            Field(new HCall { Method = targetMethod, Type = pair.Sig }, field), Field(targetGetter.Source, field)));
        Check(!Fold(targetGetter, targetAt), "destination getter evaluation count is not changed");

        var inner = Define("Inner", true, ("version", Int));
        var outer = Define("Outer", true, ("inner", inner.Sig), ("token", Short));
        var mutatedLocal = FixtureOf(outer);
        var localValues = ReadFields(mutatedLocal);
        mutatedLocal.Block.Statements.Add(new HAssign(Field(localValues[0], inner.Fields[0]), new HConst(7, Int)));
        Check(!Fold(mutatedLocal, WriteFields(mutatedLocal, localValues)), "single-assignment struct local can still have mutated fields");

        var generic = Define("Pair`1", true, ("source", Object), ("token", Short));
        generic.GenericParameters = [new GenericParam { Name = "T", OwnerType = generic }];
        var ofInt = Key(new GenericInstSig(generic, [Int]), "Pair<int>");
        var ofBool = Key(new GenericInstSig(generic, [Bool]), "Pair<bool>");
        var exact = FixtureOf(generic, ofInt);
        Check(Fold(exact, WriteFields(exact, ReadFields(exact))), "exact constructed generic whole copy is recovered");
        var mismatch = FixtureOf(generic, ofInt);
        var wrong = Local(mismatch.Method.NewLocal(ofBool));
        Check(!Fold(mismatch, WriteFields(mismatch, generic.Fields.Select(f => (HExpr)Field(wrong, f)).ToArray())), "different generic arguments do not match");
        Cases.Add(new { name = "copy_semantics", result = "dominance, alias, conversion and evaluation-order checks" });
    }

    private static LayoutCalculator TestLayouts(TypeSig root)
    {
        var layouts = (LayoutCalculator)RuntimeHelpers.GetUninitializedObject(typeof(LayoutCalculator));
        var cache = new Dictionary<TypeSig, TypeLayout>();
        typeof(LayoutCalculator).GetField("_cache", All)!.SetValue(layouts, cache);
        TypeLayout Build(TypeSig type)
        {
            if (cache.TryGetValue(type, out var known)) return known;
            var result = new TypeLayout { Known = false };
            cache[type] = result;
            int offset = 0, align = 1;
            var fields = new List<FieldSlot>();
            foreach (FieldDef field in type.Definition!.Fields.Where(f => !f.IsStatic))
            {
                TypeSig fieldType = Signatures.Substitute(field.Type, type is GenericInstSig generic ? generic.Arguments : [], []);
                int size = fieldType is PrimitiveSig primitive ? primitive.SizeOf(8) :
                    fieldType.Definition is { IsValueType: true, IsEnum: false } ? Build(fieldType).Size : 8;
                int fieldAlign = Math.Min(Math.Max(size, 1), 8);
                offset = (offset + fieldAlign - 1) / fieldAlign * fieldAlign;
                fields.Add(new FieldSlot(field, fieldType, offset, size));
                offset += size;
                align = Math.Max(align, fieldAlign);
            }
            result.Fields = [.. fields]; result.Align = align; result.DataSize = offset;
            result.Size = (offset + align - 1) / align * align; result.Known = true;
            return result;
        }
        Build(root);
        return layouts;
    }

    private static bool Snapshot(Fixture fixture, LayoutCalculator layouts) =>
        (bool)Snapshots.GetMethod("Run", All)!.Invoke(null, [fixture.Method, layouts])!;

    private static HExpr Rebase(HExpr value, HExpr from, HExpr to)
    {
        if (ReferenceEquals(value, from)) return to;
        var field = (HField)value;
        return new HField { Object = Rebase(field.Object!, from, to), Field = field.Field,
            DeclaringType = field.DeclaringType, Type = field.Type };
    }

    private static void WholeSnapshotCases()
    {
        var pair = Define("SavedPair", true, ("source", Object), ("token", Short));
        var good = FixtureOf(pair);
        var values = ReadFields(good);
        good.Block.Statements.Add(new HAssign(good.Source, Zero(pair.Sig)));
        int at = WriteFields(good, values);
        good.Block.Statements.Add(new HReturn(good.Destination));
        var layouts = TestLayouts(pair.Sig);
        Check(Snapshot(good, layouts), "complete saved fields receive a typed snapshot");
        Check(good.Block.Statements[0] is HAssign { Target: HLocal { Type: var type }, Value: HField } && type!.Key == pair.Sig.Key,
            "snapshot is inserted at the first read with the exact value type");
        Check(!Snapshot(good, layouts), "repeating snapshot recovery makes no further change");
        Check(Fold(good, at + 1), "existing copy recovery folds the untouched saved value across the original clear");
        var source = new object();
        var execution = new Machine(good, [source, (short)1977]);
        execution.Run();
        Check(ReferenceEquals(execution.Destination[pair.Fields[0]], source) && Equals(execution.Destination[pair.Fields[1]], (short)1977),
            "whole copy preserves reference identity and nonzero token");
        Check(execution.Source.Values.All(v => v is null || Equals(v, (short)0)), "whole snapshot retains the original clear");

        void Reject(string name, Action<Fixture, List<HExpr>, LayoutCalculator> change)
        {
            var fixture = FixtureOf(pair);
            var held = ReadFields(fixture);
            var shape = TestLayouts(pair.Sig);
            change(fixture, held, shape);
            fixture.Block.Statements.Add(new HAssign(fixture.Source, Zero(pair.Sig)));
            WriteFields(fixture, held);
            Check(!Snapshot(fixture, shape), name);
        }
        Reject("partial field coverage is rejected", (f, _, _) => f.Block.Statements.RemoveAt(1));
        Reject("clear inside the read window is rejected", (f, _, _) => f.Block.Statements.Insert(1, new HAssign(f.Source, Zero(pair.Sig))));
        Reject("alias store inside read window is rejected", (f, _, _) => f.Block.Statements.Insert(1,
            new HAssign(new HDeref(new HArg(0) { Type = new ByRefSig(pair.Sig) }) { Type = pair.Sig }, Zero(pair.Sig))));
        Reject("unknown call inside read window is rejected", (f, _, _) => f.Block.Statements.Insert(1,
            new HEval(new HCall { Method = new MethodDef { Name = "Unknown", DeclaringType = pair }, This = f.State })));
        Reject("mixed struct sources do not establish full coverage", (f, _, _) =>
            ((HAssign)f.Block.Statements[1]).Value = Field(Field(new HArg(1) { Type = f.State.Type }, f.State.Type!.Definition!.Fields[0]), pair.Fields[1]));
        Reject("duplicate reads do not establish a whole-value copy", (f, _, _) => f.Block.Statements.Insert(1,
            new HAssign(Local(f.Method.NewLocal(Object)), Field(f.Source, pair.Fields[0]))));
        Reject("unknown layout is rejected", (_, _, shape) => shape.Of(pair.Sig).Known = false);
        Reject("overlapping layout is rejected", (_, _, shape) => {
            var field = shape.Of(pair.Sig).Fields[1];
            shape.Of(pair.Sig).Fields[1] = field with { Offset = 0 };
        });
        Reject("getter names do not prove field reads", (f, _, _) => ((HAssign)f.Block.Statements[1]).Value = new HCall {
            Method = new MethodDef { Name = "get_token", DeclaringType = pair, ReturnType = Short }, This = f.Source, Type = Short });
        Reject("converted fields do not prove exact coverage", (f, _, _) => ((HAssign)f.Block.Statements[1]).Value =
            new HConv(HConvKind.U1, Field(f.Source, pair.Fields[1])) { Type = Primitive(Il2CppTypeEnum.U1) });
        Reject("field type mismatch is rejected", (f, _, _) => ((HAssign)f.Block.Statements[1]).Value = Field(f.Source, pair.Fields[1], Bool));
        Reject("reads from different control-flow blocks are rejected", (f, _, _) => {
            var other = new HBlock { Id = 1 };
            other.Statements.Add(f.Block.Statements[1]); f.Block.Statements.RemoveAt(1); f.Method.Blocks.Add(other);
        });
        var unchanged = FixtureOf(pair);
        WriteFields(unchanged, ReadFields(unchanged));
        Check(!Snapshot(unchanged, TestLayouts(pair.Sig)), "unchanged sources do not acquire redundant snapshots");

        // Closed generic awaiter -> task<T> -> a complete result substruct. The layout supplies substituted
        // types; a whole EntityId read must count as its subtree, not require invented primitive reads.
        var entity = Define("EntityId", true, ("data", Int));
        var task = Define("Task`1", true);
        var taskParameter = new GenericParam { Index = ++definitionIndex, Name = "T", Position = 0, OwnerType = task };
        task.GenericParameters = [taskParameter];
        task.Fields = [new FieldDef { Name = "source", DeclaringType = task, Type = Object, Attrs = FieldDef.InitOnly },
            new FieldDef { Name = "result", DeclaringType = task, Type = Signatures.GenericParam(taskParameter), Attrs = FieldDef.InitOnly },
            new FieldDef { Name = "token", DeclaringType = task, Type = Short, Attrs = FieldDef.InitOnly }];
        var awaiter = Define("Awaiter`1", true);
        var awaiterParameter = new GenericParam { Index = ++definitionIndex, Name = "T", Position = 0, OwnerType = awaiter };
        awaiter.GenericParameters = [awaiterParameter];
        awaiter.Fields = [new FieldDef { Name = "task", DeclaringType = awaiter,
            Type = Signatures.GenericInst(task, [Signatures.GenericParam(awaiterParameter)]), Attrs = FieldDef.InitOnly }];
        var closed = Signatures.GenericInst(awaiter, [entity.Sig]);
        var generic = FixtureOf(awaiter, closed);
        var genericLayouts = TestLayouts(closed);
        FieldSlot taskSlot = genericLayouts.Of(closed).Fields[0];
        HExpr taskValue = Field(generic.Source, awaiter.Fields[0], taskSlot.Type);
        var reads = new List<(HExpr Field, HExpr Held)>();
        foreach (FieldSlot field in genericLayouts.Of(taskSlot.Type).Fields)
        {
            HExpr read = Field(taskValue, field.Field, field.Type);
            HExpr held = Local(generic.Method.NewLocal(field.Type));
            generic.Block.Statements.Add(new HAssign(held, read)); reads.Add((read, held));
        }
        generic.Block.Statements.Add(new HAssign(generic.Source, Zero(closed)));
        foreach (var read in reads) generic.Block.Statements.Add(new HAssign(Rebase(read.Field, generic.Source, generic.Destination), read.Held));
        Check(Snapshot(generic, genericLayouts), "nested generic and complete substruct reads establish full coverage");
        Check(generic.Block.Statements[0] is HAssign { Target: HLocal { Type: var captured } } && captured!.Key == closed.Key,
            "largest complete generic owner is captured, not its task/result fragment");
        Check(!Snapshot(generic, genericLayouts), "nested generic snapshot recovery is a fixed point");
        var taskData = new Dictionary<FieldDef, object?> { [task.Fields[0]] = source,
            [task.Fields[1]] = new Dictionary<FieldDef, object?> { [entity.Fields[0]] = 901 }, [task.Fields[2]] = (short)2367 };
        var nestedExecution = new Machine(generic, [taskData]); nestedExecution.Run();
        var copiedTask = (Dictionary<FieldDef, object?>)nestedExecution.Destination[awaiter.Fields[0]]!;
        Check(ReferenceEquals(copiedTask[task.Fields[0]], source) && Equals(copiedTask[task.Fields[2]], (short)2367) &&
            Equals(((Dictionary<FieldDef, object?>)copiedTask[task.Fields[1]]!)[entity.Fields[0]], 901), "generic nested result/source/token values survive clear");
        Cases.Add(new { name = "typed_whole_snapshots", result = "complete layout paths, conservative rejection and fixed-point semantics" });
    }

    // A deliberately small HIR interpreter: the assertions compare observable field values and call
    // counts, rather than asserting the implementation's statement count or local names.
    private sealed class Machine
    {
        private readonly Fixture fixture;
        private readonly Dictionary<HVar, object?> locals = [];
        private readonly Dictionary<FieldDef, object?> state;
        private readonly Dictionary<FieldDef, object?> initial;
        public int Calls;
        public Dictionary<FieldDef, object?> Source => (Dictionary<FieldDef, object?>)state[fixture.State.Type!.Definition!.Fields[0]]!;
        public Dictionary<FieldDef, object?> Destination => (Dictionary<FieldDef, object?>)locals[fixture.Destination.Variable]!;
        public Machine(Fixture fixture, object?[] values)
        {
            this.fixture = fixture;
            initial = fixture.Struct.Fields.Select((field, i) => (field, values[i])).ToDictionary(x => x.field, x => x.Item2);
            state = new() { [fixture.State.Type!.Definition!.Fields[0]] = Clone(initial, fixture.Source.Type),
                [fixture.State.Type.Definition.Fields[1]] = 0 };
            locals[fixture.Destination.Variable] = Default(fixture.Destination.Type!);
        }
        private static TypeSig FieldType(TypeSig type, FieldDef field) =>
            Signatures.Substitute(field.Type, type is GenericInstSig generic ? generic.Arguments : [], []);
        private static object? Default(TypeSig type) => type.Definition is { IsValueType: true } definition
            ? definition.Fields.ToDictionary(f => f, f => Default(FieldType(type, f)))
            : type is PrimitiveSig p ? p.Element switch { Il2CppTypeEnum.I2 => (short)0, Il2CppTypeEnum.I4 => 0,
                Il2CppTypeEnum.Boolean => false, _ => null } : null;
        private static object? Clone(object? value, TypeSig? type) => type?.IsValueType == true && value is Dictionary<FieldDef, object?> fields
            ? fields.ToDictionary(kv => kv.Key, kv => Clone(kv.Value, FieldType(type, kv.Key))) : value;
        private object? Place(HExpr expression) => expression switch {
            HArg => state, HLocal local => locals[local.Variable],
            HField field => ((Dictionary<FieldDef, object?>)Place(field.Object!)!)[field.Field],
            HCall => Call(), _ => throw new NotSupportedException(expression.GetType().Name)
        };
        private object Call() { Calls++; return Clone(initial, fixture.Source.Type)!; }
        private object? Value(HExpr expression) => expression switch {
            HConst constant => constant.Value, HTypeExpr { Op: HTypeOp.Default } => Default(expression.Type!),
            _ => Clone(Place(expression), expression.Type)
        };
        public void Run()
        {
            foreach (HStmt statement in fixture.Block.Statements)
                if (statement is HAssign assignment)
                {
                    object? value = Value(assignment.Value);
                    if (assignment.Target is HLocal local) locals[local.Variable] = value;
                    else if (assignment.Target is HField field) ((Dictionary<FieldDef, object?>)Place(field.Object!)!)[field.Field] = value;
                    else throw new NotSupportedException(assignment.Target.GetType().Name);
                }
        }
    }

    private static void Main()
    {
        SnapshotCase("awaiter16", 16, [("source", Object, 0, 8, new object()), ("token", Short, 8, 2, (short)12345)]);
        SnapshotCase("scene_awaiter32", 32, [("source", Object, 0, 8, new object()), ("scene", Int, 8, 4, 817),
            ("release", Bool, 12, 1, true), ("operation", Object, 16, 8, new object()), ("token", Short, 24, 2, (short)23456)]);
        SnapshotCase("handle_awaiter40", 40, [("source", Object, 0, 8, new object()), ("internalOp", Object, 8, 8, new object()),
            ("version", Int, 16, 4, 927), ("location", String, 24, 8, "podium-skin"), ("token", Short, 32, 2, (short)31415)]);
        CopyCases();
        WholeSnapshotCases();
        Console.WriteLine(JsonSerializer.Serialize(new { passed = true, assertions, cases = Cases,
            scope = "synthetic IR semantics; original PAP native/IL evidence is documented in README" }));
    }
}
