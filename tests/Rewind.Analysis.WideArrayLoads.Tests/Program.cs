using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

// Only the new array-width recovery boundary. The fixture calls the real address resolver, load semantic
// builder, materialization planner and snapshot emitter; the memory oracle is ordinary CLR arrays.
internal static class Program
{
    private const BindingFlags All = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
    private static readonly Assembly Analysis = typeof(HirBuilder).Assembly;
    private static readonly Type Val = Analysis.GetType("Rewind.Analysis.Recover.SVal", true)!;
    private static readonly Type Parts = Analysis.GetType("Rewind.Analysis.Recover.SParts", true)!;
    private static readonly SigFactory Sigs = new();
    private static readonly PrimitiveSig Int = Sigs.Primitive(Il2CppTypeEnum.I4);
    private static readonly PrimitiveSig Float = Sigs.Primitive(Il2CppTypeEnum.R4);
    private static readonly List<object> Groups = [];
    private static int assertions;

    private static void Check(bool value, string text)
    {
        assertions++;
        if (!value) throw new InvalidOperationException(text);
    }

    private static void Set(object obj, string field, object? value) => obj.GetType().GetField(field, All)!.SetValue(obj, value);
    private static void Backing(object obj, string property, object value) => Set(obj, "<" + property + ">k__BackingField", value);
    private static object Call(object obj, string method, params object?[] args)
    {
        try { return obj.GetType().GetMethods(All).Single(m => m.Name == method && m.GetParameters().Length == args.Length).Invoke(obj, args)!; }
        catch (TargetInvocationException e) when (e.InnerException != null)
        {
            System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(e.InnerException).Throw();
            throw;
        }
    }
    private static object Meaning(HExpr e) => Activator.CreateInstance(Val, e)!;
    private static HExpr Expression(object value) => (HExpr)Val.GetField("Expr")!.GetValue(value)!;
    private static void Collections(object obj)
    {
        foreach (FieldInfo field in obj.GetType().GetFields(All).Where(f => !f.IsStatic))
        {
            Type t = field.FieldType;
            if (t.IsGenericType && t.GetGenericTypeDefinition() is var generic &&
                (generic == typeof(Dictionary<,>) || generic == typeof(List<>) || generic == typeof(HashSet<>)))
                field.SetValue(obj, Activator.CreateInstance(t));
        }
    }

    private sealed class Fixture
    {
        public HirBuilder Builder { get; }
        public HMethod Method { get; }
        public HBlock Block { get; } = new();
        public Function Function { get; } = new() { Regs = RegisterModel.Arm64 };
        public Block IrBlock { get; } = new();
        public IrBuilder Ir { get; }
        public TypeSig Element { get; }
        public HExpr ArrayExpr { get; }
        public HExpr IndexExpr { get; }
        public Node Load { get; }
        public Node Low { get; }
        public Node High { get; }
        public IDictionary Meanings { get; }
        public HashSet<Node> Planned { get; }

        public Fixture(Il2CppTypeEnum element = Il2CppTypeEnum.R4, int width = 8, int? scale = null,
            int displacement = 0, bool twoUses = true, bool arrayCall = false, bool indexCall = false,
            bool wideIndex = false, bool arrayField = false, bool indexField = false, bool readOnlyField = true)
        {
            Element = Sigs.Primitive(element);
            TypeSig arrayType = Sigs.SzArray(Element);
            var owner = new TypeDef { Name = "ArrayFixture", Assembly = new AssemblyModel { Name = "Fixture" } };
            owner.Sig = Sigs.TypeDef(owner);
            var method = new MethodDef { Name = "Read", DeclaringType = owner, ReturnType = Float };
            Method = new HMethod { Method = method }; Method.Blocks.Add(Block);
            Builder = (HirBuilder)RuntimeHelpers.GetUninitializedObject(typeof(HirBuilder)); Collections(Builder);
            var model = (Il2CppModel)RuntimeHelpers.GetUninitializedObject(typeof(Il2CppModel)); Collections(model); Backing(model, "Sigs", Sigs);
            var layouts = (LayoutCalculator)RuntimeHelpers.GetUninitializedObject(typeof(LayoutCalculator)); Collections(layouts);
            Set(layouts, "_model", model); Set(layouts, "_ptr", 8); Set(layouts, "_header", 16);
            var program = (ProgramAnalysis)RuntimeHelpers.GetUninitializedObject(typeof(ProgramAnalysis));
            Backing(program, "Model", model); Backing(program, "Layouts", layouts);
            Set(Builder, "_p", program); Set(Builder, "_m", model); Set(Builder, "_method", method);
            Set(Builder, "_h", Method); Set(Builder, "_cur", Block); Set(Builder, "_fn", Function);
            // Unresolved addresses still visit BinarySem when constructing their opaque marker. Supply
            // the same empty normalization context the real pipeline has, rather than a null fixture field.
            Set(Builder, "_l", new LiftedMethod { Method = method, Function = Function, Normalization = new NormalizeResult() });
            Set(Builder, "_ptr", 8); Set(Builder, "_header", 16);
            foreach (var pair in new (string, Il2CppTypeEnum)[] {
                ("_int", Il2CppTypeEnum.I4), ("_uint", Il2CppTypeEnum.U4), ("_long", Il2CppTypeEnum.I8), ("_ulong", Il2CppTypeEnum.U8),
                ("_float", Il2CppTypeEnum.R4), ("_double", Il2CppTypeEnum.R8), ("_bool", Il2CppTypeEnum.Boolean),
                ("_byte", Il2CppTypeEnum.U1), ("_sbyte", Il2CppTypeEnum.I1), ("_short", Il2CppTypeEnum.I2), ("_ushort", Il2CppTypeEnum.U2),
                ("_char", Il2CppTypeEnum.Char), ("_nint", Il2CppTypeEnum.I), ("_object", Il2CppTypeEnum.Object), ("_void", Il2CppTypeEnum.Void) })
                Set(Builder, pair.Item1, Sigs.Primitive(pair.Item2));
            Meanings = (IDictionary)typeof(HirBuilder).GetField("_sem", All)!.GetValue(Builder)!;
            Planned = (HashSet<Node>)typeof(HirBuilder).GetField("_materialize", All)!.GetValue(Builder)!;
            Function.Blocks.Add(IrBlock); Ir = new IrBuilder(Function) { Current = IrBlock, CurrentAddr = 0x1000 };
            Node arrayNode = Function.NewNode(Op.Param, VT.I64, null);
            Node indexNode = Function.NewNode(Op.Param, VT.I32, null);
            HField StaticField(string name, TypeSig type) => new() { Field = new FieldDef { Name = name, Type = type, DeclaringType = owner,
                Attrs = (ushort)(FieldDef.Static | (readOnlyField ? FieldDef.InitOnly : 0)) }, Type = type };
            ArrayExpr = arrayCall ? new HCall { Method = new MethodDef { Name = "GetArray", DeclaringType = owner, ReturnType = arrayType }, Type = arrayType }
                : arrayField ? StaticField("FixtureArray", arrayType) : new HArg(0) { Type = arrayType };
            TypeSig indexType = wideIndex ? Sigs.Primitive(Il2CppTypeEnum.I8) : Int;
            IndexExpr = indexCall ? new HCall { Method = new MethodDef { Name = "GetIndex", DeclaringType = owner, ReturnType = indexType }, Type = indexType }
                : indexField ? StaticField("FixtureIndex", indexType) : new HArg(1) { Type = indexType };
            Meanings[arrayNode] = Meaning(ArrayExpr); Meanings[indexNode] = Meaning(IndexExpr);
            int step = scale ?? ((PrimitiveSig)Element).SizeOf(8);
            Node address = Ir.Add(Ir.Add(arrayNode, Ir.Const(VT.I64, 32 + displacement)),
                Ir.Mul(Ir.Raw(Op.SExt, VT.I64, indexNode), Ir.Const(VT.I64, step)));
            Load = Ir.Raw(Op.Load, VTExtensions.IntOfBytes(width), address);
            VT half = VTExtensions.IntOfBytes(width / 2);
            Low = Ir.Raw(Op.Trunc, half, Load);
            Node shifted = Ir.Raw(Op.ShrU, Load.Type, Load, Ir.Const(Load.Type, width * 4));
            High = Ir.Raw(Op.Trunc, half, shifted);
            if (!twoUses) { IrBlock.Nodes.Remove(shifted); IrBlock.Nodes.Remove(High); }
            var uses = (Dictionary<Node, List<Node>>)typeof(HirBuilder).GetField("_uses", All)!.GetValue(Builder)!;
            var positions = (Dictionary<Node, int>)typeof(HirBuilder).GetField("_position", All)!.GetValue(Builder)!;
            for (int i = 0; i < IrBlock.Nodes.Count; i++)
            {
                Node n = IrBlock.Nodes[i]; positions[n] = i;
                foreach (Node input in n.In) { if (!uses.TryGetValue(input, out var list)) uses[input] = list = []; list.Add(n); }
            }
            Call(Builder, "DecideMaterialization");
        }

        public object Read() => Call(Builder, "LoadSem", Load);
        public object Snapshot(object value)
        {
            Check(Parts.IsInstanceOfType(value), "snapshot input was proved to cover every entry");
            // Exercise the same entry point ProcessBlock uses, including its Compute/LoadSem path.
            Call(Builder, "Materialize", Load);
            return Meanings[Load]!;
        }
        public HExpr FloatLane(Node lane)
        {
            Node convert = Ir.Raw(Op.BitsToF, VT.F32, lane);
            return Expression(Call(Builder, "Eval", convert));
        }
    }

    private static (int Offset, int Size, HExpr Value)[] ReadParts(object parts) =>
        ((IEnumerable)Parts.GetField("Parts")!.GetValue(parts)!).Cast<object>().Select(p =>
            ((int)p.GetType().GetProperty("Offset")!.GetValue(p)!, (int)p.GetType().GetProperty("Size")!.GetValue(p)!,
                (HExpr)p.GetType().GetProperty("Value")!.GetValue(p)!)).ToArray();

    private sealed class Machine(Array? array, int index)
    {
        public readonly Dictionary<HVar, object?> Locals = [];
        public readonly List<int> Reads = [];
        public object? Eval(HExpr e) => e switch
        {
            HArg { Index: 0 } => array,
            HArg { Index: 1 } => index,
            HField { Field.Name: "FixtureArray" } => array,
            HField { Field.Name: "FixtureIndex" } => index,
            HConst c => c.Value,
            HLocal l => Locals[l.Variable],
            HElement element => Read(element),
            HBinary { Op: HBinaryOp.Add } add => unchecked(Convert.ToInt32(Eval(add.Left)) + Convert.ToInt32(Eval(add.Right))),
            _ => throw new InvalidOperationException("Unexpected HIR in memory fixture: " + e.GetType().Name),
        };
        private object? Read(HElement element)
        {
            var source = (Array?)Eval(element.Array);
            int at = Convert.ToInt32(Eval(element.Index));
            if (source == null) throw new NullReferenceException();
            if ((uint)at >= (uint)source.Length) throw new IndexOutOfRangeException();
            Reads.Add(at); return source.GetValue(at);
        }
        public void Run(HBlock block)
        {
            foreach (HStmt statement in block.Statements)
            {
                if (statement is HAssign { Target: HLocal local, Value: var value }) Locals[local.Variable] = Eval(value);
                else throw new InvalidOperationException("Unexpected fixture statement");
            }
        }
    }

    private static void FloatPairs()
    {
        int[] bits = [0, int.MinValue, 0x3F800000, unchecked((int)0xBF400000), 0x7FC12345, unchecked((int)0xFFC54321), 0x7F800000, unchecked((int)0xFF800000)];
        foreach (int a in bits) foreach (int b in bits)
        {
            var f = new Fixture();
            Check(f.Planned.Contains(f.Load), "two real IR users plan the wide-load snapshot");
            object raw = f.Read(); Check(Parts.IsInstanceOfType(raw), "float[] word resolves as two parts");
            var parts = ReadParts(raw);
            Check(parts.Length == 2 && parts[0].Offset == 0 && parts[1].Offset == 4 && parts.All(p => p.Size == 4), "exact lane byte ranges");
            object held = f.Snapshot(raw);
            Check(ReadParts(held).All(p => p.Value is HLocal && ReferenceEquals(p.Value.Type, Float)), "typed float snapshots");
            float[] memory = [23f, BitConverter.Int32BitsToSingle(a), BitConverter.Int32BitsToSingle(b), 42f];
            var machine = new Machine(memory, 1); machine.Run(f.Block);
            HExpr low = f.FloatLane(f.Low), high = f.FloatLane(f.High);
            Check(BitConverter.SingleToInt32Bits((float)machine.Eval(low)!) == a, "low lane keeps float bits");
            Check(BitConverter.SingleToInt32Bits((float)machine.Eval(high)!) == b, "high lane is adjacent float including NaN payload/sign zero");
            Check(machine.Reads.SequenceEqual([1, 2]), "two adjacent entries are read once in order");
            memory[1] = 0f; memory[2] = 0f;
            Check(BitConverter.SingleToInt32Bits((float)machine.Eval(low)!) == a && BitConverter.SingleToInt32Bits((float)machine.Eval(high)!) == b,
                "both loaded values survive later aliasing stores");
            Check(machine.Reads.Count == 2, "consumers do not reread mutated memory");
            Check(f.Method.Problems.Count == 0, "supported float pair has no diagnostic");
        }
    }

    private static void PrimitiveRanges()
    {
        (Il2CppTypeEnum Element, Array Values)[] examples = [
            (Il2CppTypeEnum.I1, new sbyte[] { -1, 0, 1, -128, 127, -2, 3, 4 }),
            (Il2CppTypeEnum.U1, new byte[] { 255, 0, 1, 128, 127, 2, 3, 4 }),
            (Il2CppTypeEnum.I2, new short[] { -1, -32768, 32767, 3 }),
            (Il2CppTypeEnum.U2, new ushort[] { 65535, 32768, 1, 3 }),
            (Il2CppTypeEnum.Char, new char[] { '\0', '\uffff', '\u8000', 'a' }),
            (Il2CppTypeEnum.I4, new int[] { int.MinValue, int.MaxValue }),
            (Il2CppTypeEnum.U4, new uint[] { uint.MaxValue, 0x80000000 }),
        ];
        foreach (var (element, values) in examples)
        {
            var f = new Fixture(element); object raw = f.Read();
            Check(Parts.IsInstanceOfType(raw), element + " is an exact primitive range");
            var parts = ReadParts(f.Snapshot(raw)); var machine = new Machine(values, 0); machine.Run(f.Block);
            Check(parts.Length == values.Length && machine.Reads.SequenceEqual(Enumerable.Range(0, values.Length)), "all entries in an eight-byte range are loaded");
            for (int i = 0; i < parts.Length; i++) Check(Equals(machine.Eval(parts[i].Value), values.GetValue(i)), element + " entry " + i);
        }
        foreach (int width in new[] { 2, 4 })
        {
            var f = new Fixture(Il2CppTypeEnum.U1, width); var parts = ReadParts(f.Read());
            Check(parts.Length == width && parts.Select(p => p.Offset).SequenceEqual(Enumerable.Range(0, width)), "smaller complete primitive range " + width);
        }
        var immutable = new Fixture(arrayField: true, indexField: true);
        var captured = ReadParts(immutable.Snapshot(immutable.Read()));
        var readonlyMachine = new Machine(new float[] { 12f, -5f, 7f }, 1); readonlyMachine.Run(immutable.Block);
        Check((float)readonlyMachine.Eval(captured[0].Value)! == -5f && (float)readonlyMachine.Eval(captured[1].Value)! == 7f,
            "readonly array and index fields retain adjacent values");
    }

    private static void FailureOrder()
    {
        foreach (var (array, index, expected, reads) in new (Array?, int, Type, int[])[] {
            (null, 0, typeof(NullReferenceException), []),
            (new float[0], 0, typeof(IndexOutOfRangeException), []),
            (new float[2], -1, typeof(IndexOutOfRangeException), []),
            (new float[2], 1, typeof(IndexOutOfRangeException), [1]),
            (new float[2], int.MaxValue, typeof(IndexOutOfRangeException), []),
        })
        {
            var f = new Fixture(); f.Snapshot(f.Read()); var m = new Machine(array, index); Exception? thrown = null;
            try { m.Run(f.Block); } catch (Exception ex) { thrown = ex; }
            Check(thrown?.GetType() == expected, "normal null/range exception at " + index);
            Check(m.Reads.SequenceEqual(reads), "no read after the first failing entry");
        }
        var shifted = new Fixture(displacement: 4); shifted.Snapshot(shifted.Read()); var good = new Machine(new float[4], 1); good.Run(shifted.Block);
        Check(good.Reads.SequenceEqual([2, 3]), "constant array displacement is preserved");
    }

    private static void ConservativeRejections()
    {
        foreach (var (name, f) in new (string, Fixture)[] {
            ("single-use range without complete snapshot", new Fixture(twoUses: false)),
            ("effectful array getter", new Fixture(arrayCall: true)),
            ("effectful index getter", new Fixture(indexCall: true)),
            ("mutable array field", new Fixture(arrayField: true, readOnlyField: false)),
            ("mutable index field", new Fixture(indexField: true, readOnlyField: false)),
            ("64-bit index coercion", new Fixture(wideIndex: true)),
            ("packed bool bits", new Fixture(Il2CppTypeEnum.Boolean)),
            ("wrong index scale", new Fixture(scale: 2)),
            ("unaligned first element", new Fixture(displacement: 2)),
        })
        {
            Console.Error.WriteLine("Rejection fixture: " + name);
            object value = f.Read();
            Check(Val.IsInstanceOfType(value) && Expression(value) is HOpaque, name + " stays explicit and unresolved");
            Check(f.Method.Problems.Count > 0 && f.Block.Statements.Count == 0, name + " diagnoses before emitting reads");
        }
        var scalar = new Fixture(width: 4);
        Check(Val.IsInstanceOfType(scalar.Read()) && Expression(scalar.Read()) is HElement, "ordinary four-byte float array read unchanged");
    }

    private static void Group(string name, Action action)
    {
        int before = assertions; action(); Groups.Add(new { name, assertions = assertions - before, passed = true });
    }

    public static int Main(string[] args)
    {
        try
        {
            string? only = args.Length == 2 && args[0] == "--group" ? args[1] : null;
            if (args.Length != 0 && only == null) throw new ArgumentException("Use --group rejections for the failed-group increment.");
            if (only == null)
            {
                Group("float-pair bits, adjacent memory and alias snapshots", FloatPairs);
                Group("complete primitive ranges at native widths", PrimitiveRanges);
                Group("null, bounds, ordering and displacement", FailureOrder);
            }
            if (only is null or "rejections") Group("unproved shapes rejected; scalar read unchanged", ConservativeRejections);
            else throw new ArgumentException("Unknown group: " + only);
            Console.WriteLine(JsonSerializer.Serialize(new { schema = "rewind-wide-array-load-tests-v1", groups = Groups.Count,
                assertions, failed = 0, cases = Groups, historical_tests_rerun = false }, new JsonSerializerOptions { WriteIndented = true }));
            return 0;
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine(ex);
            Console.WriteLine(JsonSerializer.Serialize(new { schema = "rewind-wide-array-load-tests-v1", completed_groups = Groups,
                assertions, failed = 1, historical_tests_rerun = false }, new JsonSerializerOptions { WriteIndented = true }));
            return 1;
        }
    }
}
