using System.Reflection;
using System.Runtime.Loader;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Analysis.Hir;
using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Model;
using Rewind.Output;
using Rewind.Runtime;
using FieldAttributes = Mono.Cecil.FieldAttributes;
using MethodAttributes = Mono.Cecil.MethodAttributes;
using TypeAttributes = Mono.Cecil.TypeAttributes;

// Native-free fixture: invoke the production Writer.Compare, inspect its emitted IL,
// then execute that IL. An empty initialized model supplies architecture/signature
// services; no native input, game export, or copied comparison algorithm is used.
internal static class IsInstNullCompareSmoke
{
    private static readonly PrimitiveSig ObjectType = new(Il2CppTypeEnum.Object, null);
    private static readonly PrimitiveSig BoolType = new(Il2CppTypeEnum.Boolean, null);
    private static readonly PrimitiveSig IntType = new(Il2CppTypeEnum.I4, null);
    private static readonly PrimitiveSig LongType = new(Il2CppTypeEnum.I8, null);
    private static readonly Type WriterType = typeof(BodyEmitter).GetNestedType("Writer", BindingFlags.NonPublic)!;
    private static readonly MethodInfo CompareMethod = WriterType.GetMethod("Compare", BindingFlags.Instance | BindingFlags.NonPublic)!;
    private static readonly MethodInfo ValueMethod = WriterType.GetMethod("Value", BindingFlags.Instance | BindingFlags.NonPublic)!;

    public static void Run()
    {
        using var fixture = new Fixture();
        var cases = new List<(string Name, string Target, HCompareOp Op, bool Producer)>();
        int rejected = 0;
        foreach (TypeSig target in fixture.Aggregates)
        foreach (HCompareOp op in new[] { HCompareOp.Eq, HCompareOp.Ne })
        foreach (bool reversed in new[] { false, true })
        foreach (bool typedNull in new[] { false, true })
        foreach (bool producer in new[] { false, true })
        {
            HExpr input = producer
                ? new HCall { Method = fixture.ProducerModel, Type = ObjectType }
                : new HArg(0) { Type = ObjectType };
            var test = new HTypeExpr(HTypeOp.IsInst, target, input) { Type = target };
            var nil = new HConst(null, typedNull ? target : ObjectType);
            var expression = new HCompare(op, reversed ? nil : test, reversed ? test : nil) { Type = BoolType };
            string name = "Compare_" + cases.Count;
            var method = fixture.Emit(name, expression);
            var expected = new List<Code>();
            if (reversed) expected.Add(Code.Ldnull);
            expected.Add(producer ? Code.Call : Code.Ldarg);
            expected.Add(Code.Isinst);
            if (!reversed) expected.Add(Code.Ldnull);
            expected.Add(Code.Ceq);
            if (op == HCompareOp.Ne) { expected.Add(Code.Ldc_I4_0); expected.Add(Code.Ceq); }
            expected.Add(Code.Ret);
            Require(method.Body.Instructions.Select(i => i.OpCode.Code).SequenceEqual(expected),
                name + ": changed operand order, duplicate evaluation, boxing, unboxing, or widening");
            cases.Add((name, target.Definition!.FullName, op, producer));
        }

        TypeSig aggregate = fixture.Aggregates[0];
        HExpr Test() => new HTypeExpr(HTypeOp.IsInst, aggregate, new HArg(0) { Type = ObjectType }) { Type = aggregate };
        HExpr Whole(TypeSig? annotation = null) => new HLocal(new HVar { Type = aggregate }) { Type = annotation ?? aggregate };
        void Reject(HExpr expression, TypeSig? parameter = null, bool value = false)
        {
            fixture.Reject("Reject_" + rejected++, expression, parameter ?? ObjectType, value);
        }

        // Real aggregate values still cannot participate in scalar Eq/Ne, including
        // misleading scalar annotations and a declared struct argument.
        foreach (HCompareOp op in new[] { HCompareOp.Eq, HCompareOp.Ne })
        {
            Reject(new HCompare(op, Whole(), new HConst(null, ObjectType)));
            Reject(new HCompare(op, new HConst(null, ObjectType), Whole()));
            Reject(new HCompare(op, Whole(LongType), new HConst(0L, LongType)));
            Reject(new HCompare(op, new HArg(0) { Type = LongType }, new HConst(0L, LongType)), aggregate);
            Reject(new HCompare(op, Whole(), Whole()));
            // Numeric zero is not a literal null; the exception is not a blanket IsInst exemption.
            Reject(new HCompare(op, Test(), new HConst(0, IntType)));
            Reject(new HCompare(op, new HConst(0, IntType), Test()));
            foreach (HTypeOp typeOp in new[] { HTypeOp.Box, HTypeOp.UnboxAny, HTypeOp.CastClass, HTypeOp.Default })
                Reject(new HCompare(op,
                    new HTypeExpr(typeOp, aggregate, new HArg(0) { Type = ObjectType }) { Type = aggregate },
                    new HConst(null, ObjectType)));
            Reject(new HCompare(op, new HOpaque("unrecovered struct") { Type = aggregate }, new HConst(null, ObjectType)));
        }
        foreach (HCompareOp op in new[] { HCompareOp.Lt, HCompareOp.Gt, HCompareOp.Le, HCompareOp.Ge,
                                         HCompareOp.LtUn, HCompareOp.GtUn, HCompareOp.LeUn, HCompareOp.GeUn })
        {
            Reject(new HCompare(op, Test(), new HConst(null, ObjectType)));
            Reject(new HCompare(op, new HConst(null, ObjectType), Test()));
        }
        Reject(new HConv(HConvKind.I4, Whole()) { Type = IntType }, value: true);
        Reject(new HConv(HConvKind.I4, Test()) { Type = IntType }, value: true);

        int executed = 0;
        using var bytes = new MemoryStream();
        fixture.Assembly.Write(bytes);
        bytes.Position = 0;
        var context = new AssemblyLoadContext("isinst-null-smoke", isCollectible: true);
        try
        {
            var loaded = context.LoadFromStream(bytes);
            var host = loaded.GetType("Fixture.Host", throwOnError: true)!;
            var calls = host.GetField("Calls")!;
            var produced = host.GetField("Produced")!;
            var failure = host.GetField("Failure")!;
            foreach (var test in cases)
            {
                var method = host.GetMethod(test.Name)!;
                object boxed = Activator.CreateInstance(loaded.GetType(test.Target, throwOnError: true)!)!;
                foreach (object? input in new object?[] { boxed, 17, "wrong type", null })
                {
                    calls.SetValue(null, 0);
                    produced.SetValue(null, input);
                    failure.SetValue(null, null);
                    bool actual = (bool)method.Invoke(null, [input])!;
                    bool matches = ReferenceEquals(input, boxed);
                    Require(actual == (test.Op == HCompareOp.Ne ? matches : !matches),
                        test.Name + ": wrong value for matching, mismatched, or null input");
                    Require((int)calls.GetValue(null)! == (test.Producer ? 1 : 0),
                        test.Name + ": producer evaluated an incorrect number of times");
                    executed++;
                }
                if (!test.Producer) continue;
                var sentinel = new InvalidOperationException("producer failure");
                calls.SetValue(null, 0);
                failure.SetValue(null, sentinel);
                try
                {
                    method.Invoke(null, [null]);
                    throw new Exception(test.Name + ": producer exception was swallowed");
                }
                catch (TargetInvocationException ex) when (ReferenceEquals(ex.InnerException, sentinel))
                {
                    Require((int)calls.GetValue(null)! == 1, test.Name + ": throwing producer evaluated twice");
                    executed++;
                }
                finally { failure.SetValue(null, null); }
            }
        }
        finally { context.Unload(); }
        Console.WriteLine($"ISINST_NULL_COMPARE_SMOKE_PASS emitted={cases.Count} runtime={executed} rejected={rejected}");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }

    private sealed class Fixture : IDisposable
    {
        internal readonly AssemblyDefinition Assembly;
        internal readonly TypeSig[] Aggregates;
        internal readonly MethodDef ProducerModel;
        private readonly TypeDef _hostModel = new() { Namespace = "Fixture", Name = "Host" };
        private readonly TypeDefinition _host;
        private readonly AssemblyEmitter _emitter;
        private readonly BodyEmitter _owner;

        internal Fixture()
        {
            Assembly = AssemblyDefinition.CreateAssembly(
                new AssemblyNameDefinition("IsInstNull_" + Guid.NewGuid().ToString("N"), new Version(1, 0)),
                "IsInstNull", ModuleKind.Dll);
            ModuleDefinition module = Assembly.MainModule;
            _host = new TypeDefinition("Fixture", "Host", TypeAttributes.Public | TypeAttributes.Abstract |
                TypeAttributes.Sealed, module.TypeSystem.Object);
            module.Types.Add(_host);
            _hostModel.Sig = new TypeDefSig(_hostModel);
            var types = new Dictionary<TypeDef, TypeDefinition> { [_hostModel] = _host };
            Aggregates = new TypeSig[2];
            for (int i = 0; i < Aggregates.Length; i++)
            {
                var definition = new TypeDef { Namespace = "Fixture", Name = "Aggregate" + i, IsValueType = true };
                var signature = new TypeDefSig(definition);
                definition.Sig = signature;
                var emitted = new TypeDefinition(definition.Namespace, definition.Name,
                    TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
                    module.ImportReference(typeof(ValueType)));
                emitted.Fields.Add(new FieldDefinition("Number", FieldAttributes.Public, module.TypeSystem.Int32));
                if (i != 0) emitted.Fields.Add(new FieldDefinition("Reference", FieldAttributes.Public, module.TypeSystem.Object));
                module.Types.Add(emitted);
                types.Add(definition, emitted);
                Aggregates[i] = signature;
            }

            var calls = new FieldDefinition("Calls", FieldAttributes.Public | FieldAttributes.Static, module.TypeSystem.Int32);
            var produced = new FieldDefinition("Produced", FieldAttributes.Public | FieldAttributes.Static, module.TypeSystem.Object);
            var failure = new FieldDefinition("Failure", FieldAttributes.Public | FieldAttributes.Static, module.ImportReference(typeof(Exception)));
            _host.Fields.Add(calls); _host.Fields.Add(produced); _host.Fields.Add(failure);
            var producer = new MethodDefinition("Produce", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Object);
            _host.Methods.Add(producer);
            var il = producer.Body.GetILProcessor();
            il.Emit(OpCodes.Ldsfld, calls); il.Emit(OpCodes.Ldc_I4_1); il.Emit(OpCodes.Add); il.Emit(OpCodes.Stsfld, calls);
            il.Emit(OpCodes.Ldsfld, failure); il.Emit(OpCodes.Dup);
            var noFailure = Instruction.Create(OpCodes.Pop);
            il.Emit(OpCodes.Brfalse, noFailure); il.Emit(OpCodes.Throw); il.Append(noFailure);
            il.Emit(OpCodes.Ldsfld, produced); il.Emit(OpCodes.Ret);
            ProducerModel = new MethodDef { DeclaringType = _hostModel, Name = "Produce",
                Flags = MethodDef.Static | 6, ReturnType = ObjectType };

            // The real Writer consults architecture and signature services even for
            // a simple HCall. Use normally initialized objects without loading native
            // input, then supply only this fixture's synthetic Cecil definitions.
            Il2CppModel model = EmptyModel();
            _emitter = new AssemblyEmitter(model);
            SetMap("_types", types);
            SetMap("_methods", new Dictionary<MethodDef, MethodDefinition> { [ProducerModel] = producer });
            _owner = new BodyEmitter(_emitter, model);
        }

        private static Il2CppModel EmptyModel()
        {
            // Invoke constructors rather than creating uninitialized objects: the
            // emitter also needs Binary.Version, Sigs and the model's empty maps.
            // These two constructors initialize state only; Parse/Load is not used.
            var image = new FixtureImage();
            var metadataConstructor = typeof(MetadataFile).GetConstructor(
                BindingFlags.Instance | BindingFlags.NonPublic, binder: null,
                types: [typeof(byte[]), typeof(int), typeof(int)], modifiers: null)
                ?? throw new InvalidOperationException("MetadataFile fixture constructor changed");
            var binaryConstructor = typeof(Il2CppBinary).GetConstructor(
                BindingFlags.Instance | BindingFlags.NonPublic, binder: null,
                types: [typeof(NativeImage), typeof(int)], modifiers: null)
                ?? throw new InvalidOperationException("Il2CppBinary fixture constructor changed");
            var metadata = (MetadataFile)metadataConstructor.Invoke([Array.Empty<byte>(), 31, MetaVersion.V31_1]);
            var binary = (Il2CppBinary)binaryConstructor.Invoke([image, MetaVersion.V31_1]);
            return new Il2CppModel(image, metadata, binary);
        }

        private sealed class FixtureImage : NativeImage
        {
            public override ImageFormat Format => ImageFormat.Elf;

            internal FixtureImage()
            {
                Arch = CpuArch.Arm64;
                Os = TargetOs.Android;
                PointerSize = 8;
            }
        }

        private void SetMap(string name, object map) =>
            typeof(AssemblyEmitter).GetField(name, BindingFlags.Instance | BindingFlags.NonPublic)!.SetValue(_emitter, map);

        private (object Writer, MethodDefinition Target) Writer(string name, TypeSig parameter)
        {
            var model = new MethodDef { DeclaringType = _hostModel, Name = name, Flags = MethodDef.Static | 6,
                ReturnType = BoolType, Parameters = [new ParamDef { Name = "input", Type = parameter }] };
            var target = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, Assembly.MainModule.TypeSystem.Boolean);
            target.Parameters.Add(new ParameterDefinition("input", Mono.Cecil.ParameterAttributes.None,
                _emitter.Import(Assembly.MainModule, parameter)));
            _host.Methods.Add(target);
            target.Body.InitLocals = true;
            object writer = Activator.CreateInstance(WriterType, BindingFlags.Instance | BindingFlags.Public,
                binder: null, args: [_owner, model, new HMethod { Method = model }, target, target.Body], culture: null)!;
            return (writer, target);
        }

        internal MethodDefinition Emit(string name, HCompare expression)
        {
            var (writer, target) = Writer(name, ObjectType);
            CompareMethod.Invoke(writer, [expression]);
            target.Body.GetILProcessor().Emit(OpCodes.Ret);
            return target;
        }

        internal void Reject(string name, HExpr expression, TypeSig parameter, bool value)
        {
            var (writer, target) = Writer(name, parameter);
            try
            {
                (value ? ValueMethod : CompareMethod).Invoke(writer, [expression]);
                throw new Exception(name + ": aggregate operation was accepted");
            }
            catch (TargetInvocationException ex) when (
                ex.InnerException?.GetType().Name == "CannotEmit" &&
                ex.InnerException.Message.Contains("aggregate scalar operand", StringComparison.Ordinal))
            {
                Require(target.Body.Instructions.Count == 0, name + ": rejection emitted partial IL");
            }
            finally { _host.Methods.Remove(target); }
        }

        public void Dispose() => Assembly.Dispose();
    }
}
