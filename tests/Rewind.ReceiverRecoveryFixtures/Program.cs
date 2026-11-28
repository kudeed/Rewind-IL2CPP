using System.Collections;
using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Analysis;
using Rewind.Analysis.Abi;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Model;
using Rewind.Output;
using Rewind.Runtime;
using Helpers = Rewind.Analysis.Runtime.RuntimeHelpers;
using CMethodAttributes = Mono.Cecil.MethodAttributes;
using CFieldAttributes = Mono.Cecil.FieldAttributes;

internal static class Program
{
    private const BindingFlags All = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
    private static int assertions;
    private static readonly Type Proof = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.UnusedReceiverProof")!;
    private static readonly Type SVal = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.SVal")!;

    private static string Hash(string path) => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));
    private static int Main(string[] args)
    {
        string? journal = null, report = null;
        var selected = new HashSet<string>(StringComparer.Ordinal);
        for (int i = 0; i < args.Length; i += 2)
        {
            if (i + 1 == args.Length) throw new ArgumentException("Missing option value");
            switch (args[i])
            {
                case "--group": selected.UnionWith(args[i + 1].Split(',', StringSplitOptions.RemoveEmptyEntries)); break;
                case "--journal": journal = args[i + 1]; break;
                case "--report": report = args[i + 1]; break;
                default: throw new ArgumentException("Use --group raw-proof,receiver-selection,call-semantics --journal file.jsonl --report file.json");
            }
        }
        if (journal == null) throw new ArgumentException("--journal is required; successful groups are never rerun for the same binaries/fixture.");
        var identity = new
        {
            fixture_sha256 = Hash(Assembly.GetExecutingAssembly().Location),
            analysis_sha256 = Hash(typeof(HirBuilder).Assembly.Location),
            core_sha256 = Hash(typeof(Il2CppModel).Assembly.Location),
            output_sha256 = Hash(typeof(BodyEmitter).Assembly.Location)
        };
        string key = Convert.ToHexStringLower(SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(JsonSerializer.Serialize(identity))));
        var groups = new (string Id, Action Run)[]
        {
            ("raw-proof", RawProof), ("receiver-selection", ReceiverSelection), ("call-semantics", CallSemantics)
        };
        if (selected.Except(groups.Select(g => g.Id)).Any()) throw new ArgumentException("Unknown group");
        var passed = new HashSet<string>();
        if (File.Exists(journal))
            foreach (string line in File.ReadLines(journal))
            {
                if (string.IsNullOrWhiteSpace(line)) continue;
                using JsonDocument doc = JsonDocument.Parse(line);
                var root = doc.RootElement;
                if (root.GetProperty("identity_key").GetString() == key && root.GetProperty("status").GetString() == "pass")
                    passed.Add(root.GetProperty("group").GetString()!);
            }
        var results = new List<object>();
        bool failed = false;
        foreach (var group in groups)
        {
            if (selected.Count != 0 && !selected.Contains(group.Id)) continue;
            int before = assertions;
            string? error = null;
            bool skip = passed.Contains(group.Id);
            if (!skip)
                try { group.Run(); }
                catch (Exception e) { error = e.ToString(); failed = true; }
            var row = new
            {
                identity_key = key, group = group.Id, status = skip ? "skip-pass" : error == null ? "pass" : "fail",
                assertions = assertions - before, error, utc = DateTime.UtcNow.ToString("O")
            };
            string json = JsonSerializer.Serialize(row);
            File.AppendAllText(journal, json + Environment.NewLine);
            Console.WriteLine(json);
            results.Add(row);
        }
        var summary = new { suite = "receiver-recovery-r25", identity, identity_key = key, assertions, groups = results,
            scope = "New synthetic AArch64/model and emitted-IL fixtures only; no historical suite, game/native batch or Unity." };
        string output = JsonSerializer.Serialize(summary, new JsonSerializerOptions { WriteIndented = true });
        Console.WriteLine(output);
        if (report != null) File.WriteAllText(report, output + Environment.NewLine);
        return failed ? 1 : 0;
    }

    private static void Check(bool condition, string why)
    {
        assertions++;
        if (!condition) throw new InvalidOperationException(why);
    }
    private static object? Invoke(object? target, Type type, string name, params object?[] args)
    {
        bool Fits(Type parameter, object? value)
        {
            if (parameter.IsByRef) parameter = parameter.GetElementType()!;
            if (value == null) return !parameter.IsValueType || Nullable.GetUnderlyingType(parameter) != null;
            return parameter.IsInstanceOfType(value) || (Nullable.GetUnderlyingType(parameter)?.IsInstanceOfType(value) ?? false);
        }
        MethodInfo method = type.GetMethods(All).Single(m => m.Name == name && m.GetParameters().Length == args.Length &&
            m.GetParameters().Select((p, i) => Fits(p.ParameterType, args[i])).All(x => x));
        try { return method.Invoke(target, args); }
        catch (TargetInvocationException e) when (e.InnerException != null)
        {
            System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(e.InnerException).Throw();
            throw;
        }
    }
    private static object? Invoke(object target, string name, params object?[] args) => Invoke(target, target.GetType(), name, args);
    private static void Set(object obj, string name, object value) => obj.GetType().GetField(name, All)!.SetValue(obj, value);
    private static object? Get(object obj, string name) => obj.GetType().GetField(name, All)!.GetValue(obj);

    private sealed class Image : NativeImage
    {
        public override ImageFormat Format => ImageFormat.Elf;
        public Image()
        {
            Arch = CpuArch.Arm64; PointerSize = 8; MemoryBase = 0x1000; Memory = new byte[0x1000];
            Sections.Add(new ImageSection("il2cpp", 0x1000, (ulong)Memory.Length, SectionFlags.Read | SectionFlags.Execute));
        }
        public void Code(ulong at, params uint[] words)
        {
            for (int i = 0; i < words.Length; i++)
                System.Buffers.Binary.BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(checked((int)(at - MemoryBase)) + 4 * i), words[i]);
            FunctionTable.Add(new FunctionRange(at, at + (ulong)(4 * words.Length), 0));
        }
    }

    // These are actual constructors, including the metadata/binary constructors. The empty parsed model is
    // populated with a small linked definition graph before ProgramAnalysis constructs its ABI/context/cache.
    // No uninitialized HirBuilder, ProgramAnalysis, model or emitter is used.
    private sealed class Fixture
    {
        public readonly Image Image = new();
        public readonly Il2CppModel Model;
        public readonly AssemblyModel AssemblyModel;
        public readonly TypeDef Owner, Other;
        public readonly MethodDef Ignored, ReadsThis, Forwarder, BranchReads, Unknown, Caller, CheckedCaller, SideEffect, VoidIgnored, RetX0, MoveLr, WritebackLr, AuthHint, PlainNop, Bti;
        public readonly ProgramAnalysis Analysis;
        public TypeSig Int => Model.Sigs.Primitive(Il2CppTypeEnum.I4);
        public TypeSig Bool => Model.Sigs.Primitive(Il2CppTypeEnum.Boolean);
        public TypeSig Void => Model.Sigs.Primitive(Il2CppTypeEnum.Void);

        public Fixture(bool staticCaller = false, bool otherCaller = false)
        {
            var md = (MetadataFile)typeof(MetadataFile).GetConstructor(All, null, [typeof(byte[]), typeof(int), typeof(int)], null)!
                .Invoke([new byte[32], 39, 3900]);
            var bin = (Il2CppBinary)typeof(Il2CppBinary).GetConstructor(All, null, [typeof(NativeImage), typeof(int)], null)!
                .Invoke([Image, 3900]);
            Model = new Il2CppModel(Image, md, bin);
            AssemblyModel = new AssemblyModel { Name = "ReceiverFixture" + Guid.NewGuid().ToString("N"), ImageName = "ReceiverFixture.dll" };
            Model.Assemblies = [AssemblyModel];
            Owner = Type("Owner"); Other = Type("Other");
            Ignored = Method(Owner, "Ignored", 0x1100, Int); Image.Code(0x1100, 0x528000e0, 0xd65f03c0); // mov w0,7; ret
            ReadsThis = Method(Owner, "ReadsThis", 0x1200, Int); Image.Code(0x1200, 0xf9400000, 0xd65f03c0); // ldr x0,[x0]; ret
            Forwarder = Method(Owner, "Forwarder", 0x1300, Int); Image.Code(0x1300, 0x17ffffc0); // b ReadsThis, forwarding x0
            BranchReads = Method(Owner, "BranchReads", 0x1400, Int); Image.Code(0x1400, 0x34000061, 0x528000e0, 0xd65f03c0, 0xd65f03c0);
            Unknown = Method(Owner, "Unknown", 0x1500, Int); Image.Code(0x1500, 0xffffffff, 0xd65f03c0);
            Caller = Method(otherCaller ? Other : Owner, "Caller", 0x1600, Int, staticCaller); Image.Code(0x1600, 0x52800020, 0xd65f03c0);
            SideEffect = Method(Owner, "SideEffect", 0x1700, Int, true); Image.Code(0x1700, 0x52800060, 0xd65f03c0);
            VoidIgnored = Method(Owner, "VoidIgnored", 0x1800, Void); Image.Code(0x1800, 0xd65f03c0); // untouched x0 is not a void return
            CheckedCaller = Method(Owner, "CheckedCaller", 0x1900, Int); Image.Code(0x1900, 0x52800040, 0xd65f03c0);
            RetX0 = Method(Owner, "RetX0", 0x1a00, Void); Image.Code(0x1a00, 0xd65f0000);
            MoveLr = Method(Owner, "MoveLr", 0x1b00, Void); Image.Code(0x1b00, 0xaa0003fe, 0xd65f03c0);
            WritebackLr = Method(Owner, "WritebackLr", 0x1c00, Void); Image.Code(0x1c00, 0xf84087c1, 0xd65f03c0);
            AuthHint = Method(Owner, "AuthHint", 0x1d00, Void); Image.Code(0x1d00, 0xd503233f, 0xd65f03c0);
            PlainNop = Method(Owner, "PlainNop", 0x1e00, Void); Image.Code(0x1e00, 0xd503201f, 0xd65f03c0);
            Bti = Method(Owner, "Bti", 0x1f00, Void); Image.Code(0x1f00, 0xd503245f, 0xd65f03c0);
            Analysis = new ProgramAnalysis(Model, new Helpers());
        }
        public TypeDef Type(string name)
        {
            var type = new TypeDef { Index = Model.Types.Length, Name = name, Namespace = "Fixture", Assembly = AssemblyModel,
                Token = (uint)(0x02000001 + Model.Types.Length), Flags = 1, BaseType = Model.Sigs.Primitive(Il2CppTypeEnum.Object) };
            type.Sig = Model.Sigs.TypeDef(type); Model.Types = [..Model.Types, type]; AssemblyModel.Types.Add(type);
            ((Dictionary<string, TypeDef>)Get(Model, "_typesByName")!)[type.ReflectionName] = type;
            return type;
        }
        public MethodDef Method(TypeDef type, string name, ulong address, TypeSig returns, bool isStatic = false)
        {
            var method = new MethodDef { Index = Model.Methods.Length, DeclaringType = type, Name = name, ReturnType = returns,
                Address = address, Token = (uint)(0x06000001 + Model.Methods.Length), Flags = (ushort)(6 | MethodDef.HideBySig | (isStatic ? MethodDef.Static : 0)),
                Slot = MethodDef.InvalidSlot };
            type.Methods = [..type.Methods, method]; Model.Methods = [..Model.Methods, method];
            if (address != 0) Model.MethodsByAddress[address] = [method];
            return method;
        }
        public bool Accept(MethodDef method, Function? raw = null, bool landingPad = false, FunctionRange? range = null) =>
            (bool)Invoke(null, Proof, "Accepts", raw ?? Analysis.NewLifter().Lift(method.Address), method.Address, 0,
                Analysis.Abi.For(method, [], []), landingPad, range ?? Analysis.RangeOf(method.Address), Image)!;
        public bool Closed(CallTarget target, MethodDef? method = null) => (bool)Invoke(null, Proof, "ClosedTarget", target, method ?? Ignored)!;

        public (HMethod H, HBlock Block, HCall Call, HirBuilder Builder, Node NativeCall, HExpr? CheckedOwner) Build(HExpr stale, MethodDef? target = null, bool checkedReceiver = false, bool heldLocal = false)
        {
            target ??= Ignored;
            var fn = new Function { Address = Caller.Address, End = Caller.Address + 8, Regs = RegisterModel.Arm64 };
            var block = new Block { Id = 0, Start = Caller.Address, End = Caller.Address + 8 }; fn.Blocks.Add(block);
            Node old = fn.NewNode(Op.Param, VT.I64, null);
            Node metadata = fn.NewNode(Op.Const, VT.I64, null); metadata.Imm = 0;
            Node call = fn.NewNode(Op.Call, VT.None, block, old, metadata); call.Addr = Caller.Address + 4;
            var info = new CallInfo { Target = target.Address, Slots = [new(ArgSlotKind.IntReg, 0), new(ArgSlotKind.IntReg, 1)] };
            call.Aux = info; block.Nodes.Add(call);
            Node? owner = null;
            if (checkedReceiver)
            {
                owner = fn.NewNode(Op.Param, VT.I64, null); call.In = [..call.In, owner];
                info.Slots.Add(new ArgSlot(ArgSlotKind.CheckedReceiver, 0));
            }
            var lifted = new LiftedMethod { Function = fn, Method = Caller, Abi = Analysis.Abi.For(Caller, [], []), Normalization = new NormalizeResult() };
            var builder = new HirBuilder(Analysis, lifted);
            var meanings = (IDictionary)Get(builder, "_sem")!;
            object Sem(HExpr expression) => Activator.CreateInstance(SVal, All, null, [expression], null)!;
            meanings[old] = Sem(stale);
            var h = (HMethod)Get(builder, "_h")!;
            var hb = new HBlock { Id = 0 }; h.Blocks.Add(hb);
            HExpr? checkedOwner = null;
            if (owner != null)
            {
                HVar local = h.NewLocal(Owner.Sig, "checkedOwner");
                checkedOwner = new HLocal(local) { Type = Owner.Sig };
                hb.Statements.Add(new HAssign(new HLocal(local) { Type = Owner.Sig }, new HArg(-1) { Type = Owner.Sig }));
                meanings[owner] = Sem(checkedOwner);
            }
            Set(builder, "_cur", hb); Set(builder, "_block", block); Set(builder, "_node", call); Set(builder, "_cfg", new Cfg(fn));
            ((Dictionary<Node, int>)Get(builder, "_position")!)[call] = 0;
            ((Dictionary<Block, HBlock>)Get(builder, "_hblock")!)[block] = hb;
            if (heldLocal)
            {
                Node phi = fn.NewNode(Op.Phi, VT.I64, block, old, old);
                ((Dictionary<Node, List<Node>>)Get(builder, "_heldPhiReads")!)[old] = [phi];
                Invoke(builder, "Materialize", old, Sem(stale), true);
            }
            Invoke(builder, "BuildCall", call, target, Array.Empty<TypeSig>(), Array.Empty<TypeSig>(), false, false,
                null, false, null, 0, false, false, null);
            HCall result = hb.Statements.OfType<HEval>().Select(e => e.Expression).OfType<HCall>().Last();
            return (h, hb, result, builder, call, checkedOwner);
        }
    }

    private static void RawProof()
    {
        var f = new Fixture();
        Check(f.Accept(f.Ignored), "A known bounded body overwrites incoming x0 before its meaningful return");
        Check(!f.Accept(f.ReadsThis), "Memory reads through entry x0 reject the proof");
        Check(!f.Accept(f.Forwarder), "Tail-call forwarding of x0 rejects the proof");
        Check(!f.Accept(f.BranchReads), "One branch returning entry x0 rejects an integer-returning callee");
        Check(!f.Accept(f.Unknown), "Unmodeled native instructions reject the proof");
        Check(f.Accept(f.VoidIgnored), "Untouched x0 in a raw void ReturnValues list is ABI-dead, not a machine read");
        Check(!f.Accept(f.RetX0), "RET x0 observes the receiver as a control target even for a void ABI");
        Check(!f.Accept(f.MoveLr), "MOV x30,x0 followed by RET cannot disappear as an unused SSA alias");
        Check(!f.Accept(f.WritebackLr), "A memory base writeback to x30 is not a restoration of LR");
        Check(!f.Accept(f.AuthHint), "A pointer-authentication hint cannot hide control-register inputs");
        Check(f.Accept(f.PlainNop) && f.Accept(f.Bti), "Ordinary NOP and BTI remain valid, without implicit receiver inputs");
        Check(!f.Accept(f.Ignored, landingPad: true), "Any native EH landing pad rejects, including cleanup-only paths");
        Check(!(bool)Invoke(null, Proof, "Accepts", f.Analysis.NewLifter().Lift(f.Ignored.Address), f.Ignored.Address, 0,
            f.Analysis.Abi.For(f.Ignored, [], []), false, null, f.Image)!, "Missing reliable native range rejects the proof");
        Check(!f.Accept(f.Ignored, range: new FunctionRange(0x1100, 0x1108, 0, true)), "Chained ranges cannot prove a complete callee");
        Check(!f.Accept(f.Ignored, range: new FunctionRange(0x1104, 0x1108, 0)), "Range start must match exact entry");
        Check(!f.Accept(f.Ignored, range: new FunctionRange(0x1100, 0x1104, 0)), "A block extending beyond its bound rejects");
        Function raw = f.Analysis.NewLifter().Lift(f.VoidIgnored.Address);
        Node p = raw.Params[0]; Block b = raw.Entry;
        Node phi = raw.NewNode(Op.Phi, VT.I64, b, p, p); b.Phis.Add(phi);
        Node ret = b.Nodes.Single(n => n.Op == Op.Return); ret.In[0] = phi;
        Check(f.Accept(f.VoidIgnored, raw), "Pure phi chains used only by ABI-dead return positions are harmless");
        Node store = raw.NewNode(Op.Store, VT.None, b, p, p); b.Nodes.Insert(0, store);
        Check(!f.Accept(f.VoidIgnored, raw), "A live store defeats the void-return exception");

        Check(f.Closed(new CallTarget { Methods = [f.Ignored] }), "Only one exact closed method is a target proof");
        Check(!f.Closed(new CallTarget { Methods = [f.Ignored], Forwarded = true }), "Forwarded managed targets reject");
        Check(!f.Closed(new CallTarget { Methods = [f.Ignored, f.ReadsThis] }), "Shared native bodies reject method ambiguity");
        f.Ignored.GenericParameters = [new GenericParam { Name = "T", OwnerMethod = f.Ignored, IsMethodParameter = true }];
        Check(!f.Closed(new CallTarget { Methods = [f.Ignored] }), "Open/generic method contexts reject");
        f.Ignored.GenericParameters = [];
        f.Owner.GenericParameters = [new GenericParam { Name = "T", OwnerType = f.Owner }];
        Check(!f.Closed(new CallTarget { Methods = [f.Ignored] }), "Generic declaring-class contexts reject");
        f.Owner.GenericParameters = [];
        TypeDef generic = f.Type("OpenBox`1");
        generic.GenericParameters = [new GenericParam { Name = "T", OwnerType = generic }];
        f.Ignored.ReturnType = generic.Sig;
        Check(!f.Closed(new CallTarget { Methods = [f.Ignored] }), "Bare generic return definitions are not closed despite ContainsGenericParameter being false");
        f.Ignored.ReturnType = f.Int;
        f.Ignored.Parameters = [new ParamDef { Type = f.Model.Sigs.SzArray(f.Model.Sigs.SzArray(generic.Sig)) }];
        Check(!f.Closed(new CallTarget { Methods = [f.Ignored] }), "Nested array elements cannot hide a bare generic definition");
        f.Ignored.Parameters = [];
        f.Ignored.ReturnType = f.Model.Sigs.GenericInst(generic, [f.Int, f.Bool]);
        Check(!f.Closed(new CallTarget { Methods = [f.Ignored] }), "Generic instance argument arity must exactly match its definition");
        f.Ignored.ReturnType = f.Int;
        f.Owner.Flags |= TypeDef.Interface;
        Check(!f.Closed(new CallTarget { Methods = [f.Ignored] }), "Interface-relative receivers do not become a concrete class proof");
    }

    private static void ReceiverSelection()
    {
        var f = new Fixture();
        var badBool = f.Build(new HConst(true, f.Bool));
        Check(badBool.H.Problems.Count == 0 && badBool.Call.This is HArg { Index: -1 }, "A stale bool acquires only same-class current this");
        Check(ReferenceEquals(badBool.Call.UnusedReceiverTarget, f.Ignored), "Direct marker is bound to the exact proved MethodDef");
        var array = new HVar { Name = "array", Type = f.Model.Sigs.SzArray(f.Model.Sigs.Primitive(Il2CppTypeEnum.Object)) };
        var badArray = f.Build(new HLocal(array) { Type = array.Type });
        Check(badArray.Call.ReceiverUnused && badArray.Call.This?.Type == f.Owner.Sig, "A stale object[] is never cast to the declaring class");
        var decimalType = f.Type("DecimalLike"); decimalType.IsValueType = true;
        var decimalLocal = new HVar { Name = "decimalResult", Type = decimalType.Sig };
        Check(f.Build(new HLocal(decimalLocal) { Type = decimalType.Sig }).Call.ReceiverUnused,
            "A stale Decimal-like value is not treated as an object receiver");
        Check(f.Build(new HConst(true, f.Bool), f.VoidIgnored).Call.ReceiverUnused,
            "The selection path accepts only the ABI-dead x0 return of an otherwise unused-this void callee");
        var zero = f.Build(new HConst(null, f.Model.Sigs.Primitive(Il2CppTypeEnum.Object)));
        Check(zero.Call.ReceiverUnused, "A null stale value does not introduce a replacement null check");
        var checkedValue = f.Build(new HConst(true, f.Bool), checkedReceiver: true);
        Check(!checkedValue.Call.ReceiverUnused && ReferenceEquals(checkedValue.Call.This, checkedValue.CheckedOwner) &&
              checkedValue.CheckedOwner is HLocal local && checkedValue.H.Locals.Contains(local.Variable),
            "An original checked receiver keeps its declared local identity and callvirt null check");
        var reads = f.Build(new HConst(true, f.Bool), f.ReadsThis);
        Check(!reads.Call.ReceiverUnused && reads.H.Problems.Any(p => p.Contains("object the code did not keep")), "A callee reading x0 remains a visible gap");
        var staticF = new Fixture(staticCaller: true);
        var noThis = staticF.Build(new HConst(true, staticF.Bool));
        Check(!noThis.Call.ReceiverUnused && noThis.H.Problems.Count != 0, "No same-class current this means no invented receiver");
        var otherF = new Fixture(otherCaller: true);
        var otherThis = otherF.Build(new HConst(true, otherF.Bool));
        Check(!otherThis.Call.ReceiverUnused && otherThis.H.Problems.Count != 0, "A different declaring class is not cast into a receiver");
        var effect = new HCall { Method = f.SideEffect, Type = f.Int };
        var effects = f.Build(effect);
        Check(effects.Block.Statements.Count == 2 && effects.Block.Statements[0] is HEval { Expression: HCall first } && ReferenceEquals(first, effect),
            "The original receiver's pending call is evaluated once before the recovered call");
        var held = f.Build(new HCall { Method = f.SideEffect, Type = f.Int }, heldLocal: true);
        Check(((Dictionary<Node, List<Node>>)Get(held.Builder, "_heldPhiReads")!).Count == 0 &&
              ((HashSet<Node>)Get(held.Builder, "_phiRead")!).Count == 1,
            "Replacing an apparently atomic HLocal commits its held phi reads");
        Invoke(held.Builder, "SettlePhis");
        Check(held.Block.Statements.OfType<HAssign>().Count(a => a.Value is HCall c && ReferenceEquals(c.Method, f.SideEffect)) == 1,
            "A call materialized while only looked at survives phi settlement exactly once");
        var field = new FieldDef { Name = "Value", DeclaringType = f.Owner, Type = f.Int };
        var read = f.Build(new HField { Field = field, Object = new HConst(null, f.Owner.Sig), Type = f.Int });
        Check(!read.Call.ReceiverUnused && read.H.Problems.Count != 0, "Deferred nullable field reads fail closed instead of being erased by generic purity folding");
        Type copy = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Hir.HirCopy")!;
        var copied = (HCall)Invoke(null, copy, "Of", badBool.Call, null)!;
        Check(ReferenceEquals(copied.UnusedReceiverTarget, f.Ignored), "HirCopy keeps exact direct-call proof identity");
        Check(HirPrinter.Print(copied, badBool.H).Contains("direct-unused-this"), "Canonical HIR text distinguishes the proved direct call");
    }

    private static HMethod Body(MethodDef method, params HStmt[] statements) =>
        new() { Method = method, Blocks = [new HBlock { Id = 0, Statements = statements.ToList() }] };

    private static void CallSemantics()
    {
        var f = new Fixture();
        var recovered = f.Build(new HConst(true, f.Bool));
        var emitter = new AssemblyEmitter(f.Model); emitter.Build();
        var bodyEmitter = new BodyEmitter(emitter, f.Model);
        Check(bodyEmitter.Emit(f.Ignored, Body(f.Ignored, new HReturn(new HConst(7, f.Int)))) == null, "Ignored callee emits");
        Check(bodyEmitter.Emit(f.Caller, Body(f.Caller, new HReturn(recovered.Call))) == null, "Recovered direct caller emits");
        var ordinary = new HCall { Method = f.Ignored, This = new HArg(-1) { Type = f.Owner.Sig }, Type = f.Int };
        Check(bodyEmitter.Emit(f.CheckedCaller, Body(f.CheckedCaller, new HReturn(ordinary))) == null, "Ordinary instance caller emits");
        Check(emitter[f.Caller].Body.Instructions.Any(i => i.OpCode == OpCodes.Call && i.Operand is MethodReference m && m.Name == "Ignored"), "The proven case actually emits IL call");
        Check(!emitter[f.Caller].Body.Instructions.Any(i => i.OpCode == OpCodes.Callvirt), "The proven case emits no receiver-null-check instruction");
        Check(emitter[f.CheckedCaller].Body.Instructions.Any(i => i.OpCode == OpCodes.Callvirt), "An ordinary nonvirtual method still emits IL callvirt");

        var module = emitter[f.Owner].Module;
        var counter = new FieldDefinition("Counter", CFieldAttributes.Public | CFieldAttributes.Static, module.TypeSystem.Int32);
        emitter[f.Owner].Fields.Add(counter);
        var side = emitter[f.SideEffect]; side.Body.Instructions.Clear();
        var il = side.Body.GetILProcessor(); il.Emit(OpCodes.Ldsfld, counter); il.Emit(OpCodes.Ldc_I4_1); il.Emit(OpCodes.Add);
        il.Emit(OpCodes.Stsfld, counter); il.Emit(OpCodes.Ldc_I4_3); il.Emit(OpCodes.Ret);
        var effects = f.Build(new HCall { Method = f.SideEffect, Type = f.Int });
        effects.Block.Statements.Add(new HReturn(new HConst(9, f.Int)));
        Check(bodyEmitter.Emit(f.Caller, effects.H) == null, "Preserved effect plus recovered call emits");
        string[] calls = emitter[f.Caller].Body.Instructions.Where(i => i.Operand is MethodReference && i.OpCode == OpCodes.Call)
            .Select(i => ((MethodReference)i.Operand).Name).ToArray();
        Check(calls.SequenceEqual(["SideEffect", "Ignored"]), "Emitted IL evaluates the old receiver call once and in original order");

        MethodDefinition Bridge(string name, MethodDefinition target)
        {
            var bridge = new MethodDefinition(name, CMethodAttributes.Public | CMethodAttributes.Static, module.TypeSystem.Int32);
            emitter[f.Owner].Methods.Add(bridge);
            var writer = bridge.Body.GetILProcessor(); writer.Emit(OpCodes.Ldnull); writer.Emit(OpCodes.Call, target); writer.Emit(OpCodes.Ret);
            return bridge;
        }
        Bridge("InvokeDirectOnNull", emitter[f.Caller]); Bridge("InvokeCheckedOnNull", emitter[f.CheckedCaller]);
        using var stream = new MemoryStream(); emitter.Assemblies[f.AssemblyModel].Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        Type owner = loaded.GetType("Fixture.Owner", true)!;
        Check((int)owner.GetMethod("InvokeDirectOnNull")!.Invoke(null, null)! == 9, "The actual emitted direct-call chain accepts null this");
        Check((int)owner.GetField("Counter")!.GetValue(null)! == 1, "The retained receiver effect executes exactly once");
        bool nullThrow = false;
        try { owner.GetMethod("InvokeCheckedOnNull")!.Invoke(null, null); }
        catch (TargetInvocationException e) when (e.InnerException is NullReferenceException) { nullThrow = true; }
        Check(nullThrow, "The unchanged callvirt case still throws on null");

        var retargeted = new HCall { Method = f.ReadsThis, This = new HArg(-1) { Type = f.Owner.Sig }, Type = f.Int, UnusedReceiverTarget = f.Ignored };
        Check(bodyEmitter.Emit(f.CheckedCaller, Body(f.CheckedCaller, new HReturn(retargeted)))?.Contains("proof no longer matches") == true,
            "Changing the MethodDef cannot reuse another target's unused-this proof");
        var virtualized = new HCall { Method = f.Ignored, This = new HArg(-1) { Type = f.Owner.Sig }, Type = f.Int, UnusedReceiverTarget = f.Ignored, Virtual = true };
        Check(bodyEmitter.Emit(f.CheckedCaller, Body(f.CheckedCaller, new HReturn(virtualized))) != null, "Virtual/constrained contexts cannot inherit a direct proof");
    }
}
