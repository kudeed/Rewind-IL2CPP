using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

internal static partial class Program
{
    private static readonly Type StoredSem = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.SVal", true)!;
    private static readonly Type StorePart = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.Part", true)!;
    private sealed record StructStoreFixture(HirBuilder Builder, HMethod Body, HBlock Block, LayoutCalculator Layouts,
        TypeSig Type, Node Node, HExpr Source, object Meaning);

    private static StructStoreFixture StoreFixture(TypeSig type, int bytes = 8, HExpr? source = null)
    {
        var layouts = (LayoutCalculator)RuntimeHelpers.GetUninitializedObject(typeof(LayoutCalculator));
        var cache = new Dictionary<TypeSig, TypeLayout>();
        Set(layouts, "_cache", cache); Set(layouts, "_ptr", 8); Set(layouts, "_header", 16);
        TypeLayout Layout(TypeSig current)
        {
            if (cache.TryGetValue(current, out var prior)) return prior;
            var layout = new TypeLayout(); cache[current] = layout;
            var slots = new List<FieldSlot>(); int offset = 0;
            foreach (FieldDef field in current.Definition!.Fields)
            {
                TypeSig exact = Sigs.Substitute(field.Type, current is GenericInstSig g ? g.Arguments : [], []);
                int size = exact is PrimitiveSig primitive ? primitive.SizeOf(8) : exact.IsValueType ? Layout(exact).Size : 8;
                slots.Add(new FieldSlot(field, exact, offset, size)); offset += size;
            }
            layout.Fields = [..slots]; layout.Size = offset; layout.DataSize = offset;
            return layout;
        }
        Layout(type);
        var model = (Il2CppModel)RuntimeHelpers.GetUninitializedObject(typeof(Il2CppModel)); Backing(model, "Sigs", Sigs);
        var program = (ProgramAnalysis)RuntimeHelpers.GetUninitializedObject(typeof(ProgramAnalysis));
        Backing(program, "Model", model); Backing(program, "Layouts", layouts);
        var body = new HMethod { Method = new MethodDef { Name = "Store", DeclaringType = type.Definition! } };
        var block = new HBlock(); body.Blocks.Add(block);
        var builder = (HirBuilder)RuntimeHelpers.GetUninitializedObject(typeof(HirBuilder));
        foreach (FieldInfo field in typeof(HirBuilder).GetFields(All).Where(f => !f.IsStatic))
        {
            Type ft = field.FieldType;
            if (ft.IsGenericType && ft.GetGenericTypeDefinition() is var generic &&
                (generic == typeof(Dictionary<,>) || generic == typeof(HashSet<>) || generic == typeof(List<>)))
                field.SetValue(builder, Activator.CreateInstance(ft));
        }
        Set(builder, "_p", program); Set(builder, "_m", model); Set(builder, "_h", body); Set(builder, "_cur", block);
        foreach (var entry in new[] { ("_int", Il2CppTypeEnum.I4), ("_long", Il2CppTypeEnum.I8),
            ("_float", Il2CppTypeEnum.R4), ("_double", Il2CppTypeEnum.R8), ("_byte", Il2CppTypeEnum.U1),
            ("_sbyte", Il2CppTypeEnum.I1), ("_short", Il2CppTypeEnum.I2), ("_ushort", Il2CppTypeEnum.U2),
            ("_uint", Il2CppTypeEnum.U4), ("_ulong", Il2CppTypeEnum.U8), ("_bool", Il2CppTypeEnum.Boolean),
            ("_object", Il2CppTypeEnum.Object) }) Set(builder, entry.Item1, Sigs.Primitive(entry.Item2));
        source ??= new HArg(0) { Type = type };
        var node = new Node { Op = Op.Load, Type = bytes == 4 ? VT.I32 : VT.I64, Addr = 0x1000 };
        object meaning = Activator.CreateInstance(StoredSem, source)!;
        ((IDictionary)typeof(HirBuilder).GetField("_sem", All)!.GetValue(builder)!).Add(node, meaning);
        return new StructStoreFixture(builder, body, block, layouts, type, node, source, meaning);
    }

    private static object? StoredParts(StructStoreFixture fixture, int bytes = 8) =>
        typeof(HirBuilder).GetMethod("PartsOfStoredStruct", All)!.Invoke(fixture.Builder, [fixture.Meaning, bytes, 0x1004UL]);

    private static void StoreFields(StructStoreFixture fixture, params (int Offset, int Size, HExpr Target)[] fields)
    {
        var list = (IList)Activator.CreateInstance(typeof(List<>).MakeGenericType(StorePart))!;
        foreach (var field in fields) list.Add(Activator.CreateInstance(StorePart, field.Offset, field.Size, field.Target)!);
        typeof(HirBuilder).GetMethod("StoreParts", All)!.Invoke(fixture.Builder, [list, fixture.Node, 0x1004UL]);
    }

    private sealed class StructStoreMachine
    {
        public readonly Dictionary<int, object?> Arguments = [];
        public readonly Dictionary<HVar, object?> Variables = [];
        public object? FactoryValue;
        public int Calls, Writes;
        public bool ThrowFactory;
        private static object? Copy(object? value) => value is Dictionary<FieldDef, object?> fields
            ? fields.ToDictionary(p => p.Key, p => Copy(p.Value)) : value;
        private object? Value(HExpr expression) => expression switch
        {
            HArg arg => Arguments[arg.Index], HLocal local => Variables[local.Variable], HConst c => c.Value,
            HField field => ((Dictionary<FieldDef, object?>)Value(field.Object!)!)[field.Field],
            HCall => Factory(),
            _ => throw new InvalidOperationException("unexpected store expression: " + expression.GetType().Name)
        };
        private object? Factory()
        {
            Calls++;
            if (ThrowFactory) throw new ArithmeticException("source factory");
            return Copy(FactoryValue);
        }
        public void Run(HBlock block)
        {
            foreach (HStmt statement in block.Statements)
            {
                if (statement is not HAssign assignment) throw new InvalidOperationException("unexpected store statement");
                object? value = Copy(Value(assignment.Value));
                if (assignment.Target is HLocal local) Variables[local.Variable] = value;
                else if (assignment.Target is HField field)
                {
                    ((Dictionary<FieldDef, object?>)Value(field.Object!)!)[field.Field] = value; Writes++;
                }
                else throw new InvalidOperationException("unexpected store destination");
            }
        }
    }

    private static void WholeStructStores()
    {
        TypeSig number = Sigs.Primitive(Il2CppTypeEnum.R4);
        TypeDef pair = Define("PackedPair", true, ("first", number), ("second", number));
        TypeDef triple = Define("LargerDestination", true, ("first", number), ("second", number), ("third", number));
        HExpr Destination(FieldDef field) => Field(new HArg(1) { Type = triple.Sig }, field, number);
        var factory = new MethodDef { Name = "Make", Flags = MethodDef.Static | 6, DeclaringType = pair, ReturnType = pair.Sig };
        int[] patterns = [0, unchecked((int)0x80000000), 0x3fa00000, unchecked((int)0xc1200000), 0x7fc01234, 0x7f800000, unchecked((int)0xff800000), 1];
        foreach (int pattern in patterns)
        {
            HExpr source = new HCall { Method = factory, Type = pair.Sig };
            var fixture = StoreFixture(pair.Sig, source: source);
            StoreFields(fixture, (0, 4, Destination(triple.Fields[0])), (4, 4, Destination(triple.Fields[1])));
            float first = BitConverter.Int32BitsToSingle(pattern), second = BitConverter.Int32BitsToSingle(pattern ^ int.MinValue);
            var destination = new Dictionary<FieldDef, object?> { [triple.Fields[0]] = 31f, [triple.Fields[1]] = 41f, [triple.Fields[2]] = 59f };
            var machine = new StructStoreMachine { FactoryValue = new Dictionary<FieldDef, object?> { [pair.Fields[0]] = first, [pair.Fields[1]] = second } };
            machine.Arguments[1] = destination; machine.Run(fixture.Block);
            Check(BitConverter.SingleToInt32Bits((float)destination[triple.Fields[0]]!) == pattern, "low scalar preserves every float bit");
            Check(BitConverter.SingleToInt32Bits((float)destination[triple.Fields[1]]!) == (pattern ^ int.MinValue), "high scalar preserves every float bit");
            Check(machine.Calls == 1 && machine.Writes == 2 && Equals(destination[triple.Fields[2]], 59f), "one source evaluation and only covered destination fields change");
            var throwing = new StructStoreMachine { ThrowFactory = true };
            throwing.Arguments[1] = destination;
            try { throwing.Run(fixture.Block); Check(false, "factory failure must propagate"); }
            catch (ArithmeticException) { Check(throwing.Calls == 1 && throwing.Writes == 0, "source failure precedes every destination write"); }
        }
        // A complete value snapshot prevents overlapping writes from changing a later field read.
        var alias = StoreFixture(pair.Sig);
        StoreFields(alias,
            (0, 4, Field(new HArg(0) { Type = pair.Sig }, pair.Fields[1], number)),
            (4, 4, Field(new HArg(0) { Type = pair.Sig }, pair.Fields[0], number)));
        var shared = new Dictionary<FieldDef, object?> { [pair.Fields[0]] = 11f, [pair.Fields[1]] = 23f };
        var aliasMachine = new StructStoreMachine(); aliasMachine.Arguments[0] = shared; aliasMachine.Run(alias.Block);
        Check(Equals(shared[pair.Fields[0]], 23f) && Equals(shared[pair.Fields[1]], 11f), "aliased destinations read the original complete value");

        // The proof works through exact constructed generic and nested layouts without type names.
        var wrapper = Define("Container`1", true);
        var parameter = new GenericParam { Index = ++index, Name = "T", OwnerType = wrapper, Position = 0 };
        wrapper.GenericParameters = [parameter];
        wrapper.Fields = [new FieldDef { Name = "payload", DeclaringType = wrapper, Type = Sigs.GenericParam(parameter) }];
        TypeSig instance = Sigs.GenericInst(wrapper, [pair.Sig]);
        var nested = StoreFixture(instance);
        StoreFields(nested, (0, 4, Destination(triple.Fields[0])), (4, 4, Destination(triple.Fields[1])));
        var nestedDestination = new Dictionary<FieldDef, object?> { [triple.Fields[0]] = 0f, [triple.Fields[1]] = 0f, [triple.Fields[2]] = 0f };
        var nestedMachine = new StructStoreMachine();
        nestedMachine.Arguments[0] = new Dictionary<FieldDef, object?> { [wrapper.Fields[0]] = new Dictionary<FieldDef, object?> { [pair.Fields[0]] = 17f, [pair.Fields[1]] = -29f } };
        nestedMachine.Arguments[1] = nestedDestination; nestedMachine.Run(nested.Block);
        Check(Equals(nestedDestination[triple.Fields[0]], 17f) && Equals(nestedDestination[triple.Fields[1]], -29f), "closed nested generic fields retain exact values");

        void Reject(string label, Action<StructStoreFixture> alter, TypeSig? type = null, int bytes = 8)
        {
            var fixture = StoreFixture(type ?? pair.Sig); alter(fixture);
            Check(StoredParts(fixture, bytes) == null && fixture.Block.Statements.Count == 0, label); Cases.Add(label);
        }
        Reject("unknown layout is not decomposed", f => f.Layouts.Of(f.Type).Known = false);
        Reject("partial struct word is not a complete value", _ => { }, bytes: 4);
        Reject("unproved bytes beyond a struct are retained", _ => { }, bytes: 16);
        Reject("overlapping fields are refused", f => f.Layouts.Of(f.Type).Fields[1] = f.Layouts.Of(f.Type).Fields[1] with { Offset = 0 });
        Reject("padding is not invented as field bits", f => f.Layouts.Of(f.Type).Size = 12);
        Reject("wrong scalar width is refused", f => f.Layouts.Of(f.Type).Fields[0] = f.Layouts.Of(f.Type).Fields[0] with { Size = 2 });
        var reference = Define("ReferenceBits", true, ("reference", Object));
        Reject("references never become numeric pieces", _ => { }, reference.Sig);
        var nonValue = Define("ClassBits", false, ("first", number), ("second", number));
        Reject("class values are not struct payloads", _ => { }, nonValue.Sig);
        Reject("unknown nested layout is refused", f => f.Layouts.Of(pair.Sig).Known = false, instance);
        var shortPair = Define("FourBytes", true, ("first", Sigs.Primitive(Il2CppTypeEnum.I2)), ("second", Sigs.Primitive(Il2CppTypeEnum.I2)));
        var small = StoreFixture(shortPair.Sig, bytes: 4);
        Check(StoredParts(small, 4) is IList { Count: 2 }, "complete four-byte scalar struct is supported");
        Cases.Add("wide stores of complete scalar structs: bit identity, one evaluation, aliases, nested generics and refusal cases");
    }
}
