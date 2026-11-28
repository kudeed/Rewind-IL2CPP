using System.Collections.Concurrent;
using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Abi;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;
using HostRuntime = System.Runtime.CompilerServices.RuntimeHelpers;
using Helpers = Rewind.Analysis.Runtime.RuntimeHelpers;

internal static class Program
{
    private const BindingFlags All = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
    private static int assertions;
    private static readonly string RunId = Guid.NewGuid().ToString("N");

    private static int Main(string[] args)
    {
        string? report = null, journal = null;
        var selected = new HashSet<string>(StringComparer.Ordinal);
        for (int i = 0; i < args.Length; i++)
        {
            if (i + 1 == args.Length) throw new ArgumentException("Missing option value");
            string key = args[i], value = args[++i];
            if (key == "--group") selected.UnionWith(value.Split(',', StringSplitOptions.RemoveEmptyEntries));
            else if (key == "--report") report = value;
            else if (key == "--journal") journal = value;
            else throw new ArgumentException("--group shape,identity,frame,eh,order --report file --journal jsonl");
        }
        journal ??= report == null ? null : report + ".groups.jsonl";
        string analysisHash = Hash(typeof(OutlinedCleanup).Assembly.Location), coreHash = Hash(typeof(Il2CppModel).Assembly.Location);
        string fixtureHash = Hash(typeof(Program).Assembly.Location);
        string evidenceKey = "outlined-cleanup-v1/" + analysisHash + "/" + coreHash + "/" + fixtureHash;
        var passed = new HashSet<string>(StringComparer.Ordinal);
        if (journal != null && File.Exists(journal))
            foreach (string line in File.ReadLines(journal))
            {
                if (string.IsNullOrWhiteSpace(line)) continue;
                using JsonDocument item = JsonDocument.Parse(line);
                JsonElement e = item.RootElement;
                if (e.GetProperty("evidence_key").GetString() == evidenceKey && e.GetProperty("status").GetString() == "pass")
                    passed.Add(e.GetProperty("group").GetString()!);
            }
        var groups = new (string Id, Action Run)[]
        {
            ("shape", Shape), ("identity", Identity), ("frame", Frame), ("eh", Exceptions), ("order", Order)
        };
        if (selected.Except(groups.Select(g => g.Id)).Any()) throw new ArgumentException("Unknown group");
        var results = new List<object>();
        bool failed = false;
        foreach (var group in groups)
        {
            if (selected.Count != 0 && !selected.Contains(group.Id)) continue;
            if (passed.Contains(group.Id))
            {
                var skipped = new { run_id = RunId, evidence_key = evidenceKey, group = group.Id, status = "skipped_prior_pass", assertions = 0 };
                results.Add(skipped); Console.WriteLine(JsonSerializer.Serialize(skipped)); continue;
            }
            int before = assertions;
            string? error = null;
            try { group.Run(); }
            catch (Exception e) { failed = true; error = e.ToString(); }
            var result = new { run_id = RunId, evidence_key = evidenceKey, group = group.Id, status = error == null ? "pass" : "fail", assertions = assertions - before, error };
            string json = JsonSerializer.Serialize(result);
            results.Add(result); Console.WriteLine(json);
            if (journal != null) File.AppendAllText(journal, json + Environment.NewLine);
        }
        string summary = JsonSerializer.Serialize(new
        {
            suite = "outlined-cleanup", run_id = RunId, evidence_key = evidenceKey, assertions, groups = results,
            analysis_binary_sha256 = analysisHash, core_binary_sha256 = coreHash, fixture_binary_sha256 = fixtureHash,
            scope = "New structural/identity/frame/EH/order fixtures only. No historical suites, native export or Unity."
        }, new JsonSerializerOptions { WriteIndented = true });
        Console.WriteLine(summary);
        if (report != null) File.WriteAllText(report, summary + Environment.NewLine);
        return failed ? 1 : 0;
    }

    private static string Hash(string path) => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));
    private static void Check(bool condition, string why) { assertions++; if (!condition) throw new InvalidOperationException(why); }
    private static void Set(object target, string name, object? value)
    {
        for (Type? type = target.GetType(); type != null; type = type.BaseType)
            if (type.GetField(name, All | BindingFlags.DeclaredOnly) is { } field) { field.SetValue(target, value); return; }
        throw new MissingFieldException(target.GetType().FullName, name);
    }
    private static void Backing(object target, string name, object value) => Set(target, "<" + name + ">k__BackingField", value);

    // This fixture supplies the in-memory image/model tables consumed by the real recognizer and pass.
    // ELF parsing and metadata loading have their own frozen real-input evidence; they are not re-run here.
    private sealed class Fixture
    {
        public readonly byte[] Memory = new byte[0x10000];
        public readonly ElfImage Image;
        public readonly Il2CppModel Model;
        public readonly ProgramAnalysis Analysis;
        public readonly Helpers Helpers = new();
        public readonly SigFactory Sigs = new();
        public readonly Dictionary<ulong, ItaniumExceptionTable?> Tables = [];
        public readonly ItaniumExceptionTable CallerTable = new();
        public readonly Function Fn = new() { Address = Caller, End = Caller + 0x100, Regs = RegisterModel.Arm64 };
        public readonly Block Entry = new() { Id = 0, Start = Caller, End = Caller + 0x40 },
            Body = new() { Id = 1, Start = Caller + 0x50, End = Caller + 0x58, Scope = 0 },
            Caught = new() { Id = 2, Start = Caller + 0x60, End = Caller + 0x70, Scope = 1 },
            Join = new() { Id = 3, Start = Caller + 0x80, End = Caller + 0x88 };
        public readonly Node Sp, FrameAddress, ReceiverAddress, Initializer, ZeroStore, ReceiverStore, CleanupCall, PendingStore;
        public readonly TypeDef Enumerator;
        public readonly MethodDef Dispose, GetEnumerator, MoveNext;
        public readonly MethodInst Specific;
        public readonly ulong Helper, CleanupTarget, Slot;
        public readonly int ReceiverSize;
        public const ulong Caller = 0x3000, InitTarget = 0x2100, MoveTarget = 0x2200, Rethrow = 0x2300, Got = 0x7000, InitSlot = 0x7110, MoveSlot = 0x7120;
        public const int FrameOffset = -128, ReceiverOffset = -64;

        public Fixture(int family = 0, bool copied = false)
        {
            Helper = 0x1000UL + (ulong)family * 0x100;
            CleanupTarget = 0x2000UL + (ulong)family * 0x40;
            Slot = 0x7100;
            ReceiverSize = family == 0 ? 40 : 24;
            Image = (ElfImage)HostRuntime.GetUninitializedObject(typeof(ElfImage));
            Set(Image, "Memory", Memory); Set(Image, "MemoryBase", 0UL);
            Backing(Image, "Arch", CpuArch.Arm64); Backing(Image, "PointerSize", 8); Backing(Image, "ImageBase", 0UL);
            Backing(Image, "Os", TargetOs.Android); Backing(Image, "FilePath", "outlined-cleanup-fixture");
            Backing(Image, "Sections", new List<ImageSection>
            {
                new(".text", 0x1000, 0x5000, SectionFlags.Read | SectionFlags.Execute),
                new(".data", 0x6000, 0x3000, SectionFlags.Read | SectionFlags.Write)
            });
            Backing(Image, "Exports", new Dictionary<string, ulong>()); Backing(Image, "ImportSlots", new Dictionary<ulong, string>());
            Backing(Image, "Symbols", new Dictionary<ulong, string>());
            Backing(Image, "FunctionTable", new List<FunctionRange> { new(Helper, Helper + 48, 1), new(Caller, Caller + 0x100, 2) });
            Backing(Image, "ImportStubs", new Dictionary<ulong, string>()); Backing(Image, "SlotSymbols", new Dictionary<ulong, string>());
            Set(Image, "_relro", new List<(ulong, ulong)> { (0x7000, 0x7100) }); Set(Image, "_tables", Tables);
            Set(Image, "_fdeOf", new Dictionary<ulong, ulong>());
            Tables[Helper] = null; Tables[Caller] = CallerTable;
            Word(Helper, 0xA9BF4FFE); Word(Helper + 4, Adrp(8, Helper + 4, Got)); Word(Helper + 8, 0xAA0003F3);
            Word(Helper + 12, 0xF9400108); Word(Helper + 16, 0xF9400400); Word(Helper + 20, 0xF9400101);
            Word(Helper + 24, Bl(Helper + 24, CleanupTarget)); Word(Helper + 28, 0xF9400260);
            Word(Helper + 32, 0xB5000060); Word(Helper + 36, 0xA8C14FFE); Word(Helper + 40, 0xD65F03C0);
            Word(Helper + 44, Bl(Helper + 44, Rethrow)); Word(CleanupTarget, 0xD65F03C0);
            Word(Caller + 0x60, 0xD503201F); Word(Caller + 0x70, 0xD503201F); Word(Caller + 0xE0, 0xD503201F);
            Word(Caller + 0x80, Bl(Caller + 0x80, Helper)); Pointer(Got, Slot);

            var binary = (Il2CppBinary)typeof(Il2CppBinary).GetConstructor(All, null, [typeof(NativeImage), typeof(int)], null)!.Invoke([Image, 3900]);
            Model = (Il2CppModel)HostRuntime.GetUninitializedObject(typeof(Il2CppModel));
            Backing(Model, "Image", Image); Backing(Model, "Binary", binary); Backing(Model, "Sigs", Sigs);
            Backing(Model, "MethodsByAddress", new Dictionary<ulong, List<MethodDef>>());
            Backing(Model, "InstsByAddress", new Dictionary<ulong, List<MethodInst>>());
            Set(Model, "_usageCache", new ConcurrentDictionary<ulong, MetadataUsage?>());
            Set(Model, "_typesByName", new Dictionary<string, TypeDef>(StringComparer.Ordinal));
            Model.Types = []; Model.Methods = []; Model.MethodInsts = []; Model.Fields = []; Model.Parameters = []; Model.Assemblies = []; Model.GenericParams = [];
            Enumerator = Type(family == 0 ? "Enumerator`2" : "KeyEnumerator`2", true);
            Generic(Enumerator, 0);
            Enumerator.Fields = Enumerable.Range(0, ReceiverSize / 8).Select(i => new FieldDef
            {
                Index = i, Name = "word" + i, DeclaringType = Enumerator, Type = Sigs.Primitive(Il2CppTypeEnum.I8), Offset = 16 + 8 * i
            }).ToArray();
            TypeDef collection = Type("Collection`2", false); Generic(collection, 2);
            TypeDef first = Type(family == 0 ? "TextKey" : "ObjectFieldKey", false), second = Type(family == 0 ? "OverrideValue" : "IntegerList", false);
            TypeSig[] specificArgs = [first.Sig, second.Sig], sharedArgs = [Sigs.Primitive(Il2CppTypeEnum.Object), Sigs.Primitive(Il2CppTypeEnum.Object)];
            Dispose = Method(Enumerator, "Dispose", Sigs.Primitive(Il2CppTypeEnum.Void));
            GetEnumerator = Method(collection, "GetEnumerator", Sigs.GenericInst(Enumerator, collection.GenericParameters.Select(Sigs.GenericParam).Cast<TypeSig>().ToArray()));
            MoveNext = Method(Enumerator, "MoveNext", Sigs.Primitive(Il2CppTypeEnum.Boolean));
            Specific = Inst(Dispose, specificArgs, 0);
            MethodInst shared = Inst(Dispose, sharedArgs, CleanupTarget);
            Inst(GetEnumerator, specificArgs, 0); Inst(GetEnumerator, sharedArgs, InitTarget);
            Inst(MoveNext, specificArgs, 0); Inst(MoveNext, sharedArgs, MoveTarget);
            Pointer(Slot, UsageToken(0)); Pointer(InitSlot, UsageToken(2)); Pointer(MoveSlot, UsageToken(4));
            Helpers.Add(Rethrow, new HelperInfo(HelperKind.Rethrow, 1, true, false, "fixture rethrow"));
            Analysis = (ProgramAnalysis)HostRuntime.GetUninitializedObject(typeof(ProgramAnalysis));
            var layouts = new LayoutCalculator(Model);
            Backing(Analysis, "Model", Model); Backing(Analysis, "Helpers", Helpers); Backing(Analysis, "Layouts", layouts);
            Backing(Analysis, "Abi", new Aapcs64Abi(Model, layouts)); Backing(Analysis, "Context", new ModelCodeContext(Model));
            Set(Analysis, "_outlinedCleanups", new Dictionary<ulong, OutlinedCleanup?>()); Set(Analysis, "_shapes", new Dictionary<ulong, CallShape?>());

            Fn.Blocks.AddRange([Entry, Body, Caught, Join]);
            Fn.TryRegions.Add(new TryRegionInfo { Index = 0, Funclet = Caller + 0x60 });
            Edge(Entry, Caught); Edge(Entry, Body); Edge(Body, Join); Edge(Caught, Join);
            Sp = Fn.NewNode(Op.Param, VT.I64, null); Sp.Imm = Fn.Regs.StackPointer; Fn.Params[Fn.Regs.StackPointer] = Sp;
            FrameAddress = Address(Entry, FrameOffset); ReceiverAddress = Address(Entry, ReceiverOffset);
            Node buffer = copied ? FrameAddress : ReceiverAddress;
            Initializer = Call(Entry, InitTarget, Caller + 8, [(8, buffer), (0, Const(0xA000)), (1, SlotValue(InitSlot))]);
            if (copied)
                for (int i = 0; i < ReceiverSize; i += 8)
                {
                    Node value = Add(Entry, Op.Load, VT.I64, Address(Entry, FrameOffset + i)); value.Addr = Caller + 0x10 + (ulong)i;
                    Node copy = Add(Entry, Op.Store, VT.None, Address(Entry, ReceiverOffset + i), value); copy.Addr = Caller + 0x20 + (ulong)i;
                }
            ZeroStore = Add(Entry, Op.Store, VT.None, FrameAddress, Const(0)); ZeroStore.Addr = Caller + 0x30;
            ReceiverStore = Add(Entry, Op.Store, VT.None, Address(Entry, FrameOffset + 8), ReceiverAddress); ReceiverStore.Addr = ZeroStore.Addr;
            Node gate = Add(Entry, Op.Idiom, VT.I1); gate.Imm = (long)IdiomKind.TryEntry; gate.Aux = 0;
            Add(Entry, Op.Branch, VT.None, gate);
            Call(Body, MoveTarget, Caller + 0x50, [(0, ReceiverAddress), (1, SlotValue(MoveSlot))]); Add(Body, Op.Jump, VT.None);
            Node wrapper = Add(Caught, Op.Idiom, VT.I64); wrapper.Imm = (long)IdiomKind.CaughtWrapper; wrapper.Aux = 0;
            Node pending = Add(Caught, Op.Load, VT.I64, wrapper); pending.Addr = Caller + 0x64;
            PendingStore = Add(Caught, Op.Store, VT.None, FrameAddress, pending); PendingStore.Addr = Caller + 0x68; Add(Caught, Op.Jump, VT.None);
            CleanupCall = Call(Join, Helper, Caller + 0x80, [(0, FrameAddress)]); Add(Join, Op.Return, VT.None);
            CallerTable.CallSites.AddRange([
                new(Caller + 8, Caller + 12, 0, 0),
                new(Caller + 0x50, Caller + 0x54, Caller + 0x60, 1, 1),
                new(Caller + 0x80, Caller + 0x84, 0, 0)
            ]);
        }

        private TypeDef Type(string name, bool value)
        {
            var t = new TypeDef { Index = Model.Types.Length, Name = name, IsValueType = value, Assembly = new AssemblyModel { Name = "Fixture" } };
            t.Sig = Sigs.TypeDef(t); Model.Types = [..Model.Types, t]; return t;
        }
        private void Generic(TypeDef type, int first)
        {
            type.GenericParameters = Enumerable.Range(0, 2).Select(i => new GenericParam { Index = first + i, Position = i, Name = "T" + i, OwnerType = type }).ToArray();
            Model.GenericParams = [..Model.GenericParams, ..type.GenericParameters];
        }
        private MethodDef Method(TypeDef owner, string name, TypeSig returns)
        {
            var m = new MethodDef { Index = Model.Methods.Length, Name = name, DeclaringType = owner, ReturnType = returns, Slot = MethodDef.InvalidSlot };
            owner.Methods = [..owner.Methods, m]; Model.Methods = [..Model.Methods, m]; return m;
        }
        private MethodInst Inst(MethodDef method, TypeSig[] args, ulong address)
        {
            var i = new MethodInst { SpecIndex = Model.MethodInsts.Length, Method = method, ClassArguments = args, Address = address };
            Model.MethodInsts = [..Model.MethodInsts, i]; if (address != 0) Model.InstsByAddress[address] = [i]; return i;
        }
        public void Word(ulong at, uint word) => BitConverter.GetBytes(word).CopyTo(Memory, (int)at);
        public void Pointer(ulong at, ulong word) => BitConverter.GetBytes(word).CopyTo(Memory, (int)at);
        public static ulong UsageToken(int index) => ((ulong)UsageKind.MethodRef << 29) | ((ulong)index << 1) | 1;
        public static uint Bl(ulong at, ulong target) => 0x94000000 | (uint)(((long)target - (long)at) >> 2) & 0x03FFFFFF;
        private static uint Adrp(byte rd, ulong at, ulong target)
        {
            long pages = ((long)(target & ~0xFFFUL) - (long)(at & ~0xFFFUL)) >> 12;
            return 0x90000000 | ((uint)pages & 3) << 29 | (((uint)pages >> 2) & 0x7FFFF) << 5 | rd;
        }
        public Node Const(long value, VT type = VT.I64) { Node n = Fn.NewNode(Op.Const, type, null); n.Imm = value; return n; }
        public Node SlotValue(ulong slot) { Node n = Fn.NewNode(Op.SlotValue, VT.I64, null); n.Imm = (long)slot; return n; }
        public Node Address(Block block, int offset) => Add(block, Op.Add, VT.I64, Sp, Const(offset));
        public Node Add(Block block, Op op, VT type, params Node[] inputs)
        {
            Node n = Fn.NewNode(op, type, block, inputs); block.Nodes.Add(n); return n;
        }
        public Node Call(Block block, ulong target, ulong address, (int Register, Node Value)[] args)
        {
            Node n = Add(block, Op.Call, VT.None, args.Select(a => a.Value).ToArray()); n.Addr = address;
            n.Aux = new CallInfo { Target = target, Slots = args.Select(a => new ArgSlot(ArgSlotKind.IntReg, a.Register)).ToList() }; return n;
        }
        public static void Edge(Block from, Block to) { from.Succs.Add(to); to.Preds.Add(from); }
        public OutlinedCleanup? Recognize() => OutlinedCleanup.Recognize(Analysis, Helper);
        public bool Run() => OutlinedCleanups.Run(Fn, Analysis);
        public bool OriginalCall => ((CallInfo)CleanupCall.Aux!).Target == Helper;
        public void InBody(Node node)
        {
            node.Block!.Nodes.Remove(node); node.Block = Body; Body.Nodes.Insert(Body.Nodes.Count - 1, node);
        }
        public void ProtectedCall()
        {
            InBody(CleanupCall); CleanupCall.Addr = Caller + 0x54;
            CallerTable.CallSites.Add(new(Caller + 0x54, Caller + 0x58, Caller + 0x60, 1, 1));
        }
    }

    private static void Shape()
    {
        for (int family = 0; family < 2; family++)
        {
            var f = new Fixture(family);
            OutlinedCleanup? recognized = f.Recognize();
            Check(recognized != null && recognized.ReceiverSize == f.ReceiverSize, "Each complete bounded body is recognized with its exact layout");
            Check(f.Analysis.ShapeOf(f.Helper) is { Count: 1, Returns: CallReturn.Unknown, Slots.Count: 1 }, "Only x0 is captured, while unproved result use remains observable");
        }
        void Reject(Action<Fixture> alter, string why) { var f = new Fixture(); alter(f); Check(f.Recognize() == null, why); }
        Reject(f => f.Image.FunctionTable[0] = new(f.Helper, f.Helper + 52, 1), "No following instruction is silently merged");
        Reject(f => f.Word(f.Helper + 32, 0xB4000060), "Reversed null branch is rejected");
        Reject(f => f.Word(f.Helper + 16, 0xF9400800), "Changed receiver offset is rejected");
        Reject(f => f.Word(f.Helper + 28, 0xF9000260), "An extra store cannot replace the post-call load");
        Reject(f => f.Word(f.Helper + 44, 0xD65F03C0), "A returning terminal block is rejected");
        Reject(f => f.Word(f.Helper + 40, 0xD65F0BFF), "An authenticated RET alias is not an ordinary return");
        Reject(f => f.Tables[f.Helper] = new ItaniumExceptionTable(), "A helper LSDA, including a gap-only table, is not assumed to propagate");
    }

    private static void Identity()
    {
        var positive = new Fixture();
        Check(positive.Specific.Address == 0 && ReferenceEquals(positive.Recognize()!.Method, positive.Specific), "Address-zero specific context is supplied by MethodInfo, not a direct mapping");
        void Reject(Action<Fixture> alter, string why) { var f = new Fixture(); alter(f); Check(f.Recognize() == null, why); }
        Reject(f => f.Model.MethodInsts[0] = f.Model.MethodInsts[4], "Same RET bytes do not identify a mismatched MethodRef");
        Reject(f => f.Model.InstsByAddress.Remove(f.CleanupTarget), "An unregistered body cannot be guessed from its name");
        Reject(f => f.Model.MethodInsts[1].Address = 0, "A zero-address instantiation is never a registered native body");
        Reject(f => f.Model.MethodInsts[1].ClassArguments = [f.Sigs.Primitive(Il2CppTypeEnum.I4), f.Model.MethodInsts[1].ClassArguments[1]], "Two pointer arguments do not prove compatibility with a value-type specialization");
        Reject(f =>
        {
            f.Specific.ClassArguments = [f.Enumerator.Sig, f.Specific.ClassArguments[1]];
            f.Model.MethodInsts[1].ClassArguments = [f.Enumerator.Sig, f.Model.MethodInsts[1].ClassArguments[1]];
        }, "A bare open TypeDefSig is not a closed generic argument even when both keys match");
        Reject(f =>
        {
            TypeSig malformed = f.Sigs.GenericInst(f.Enumerator, [f.Specific.ClassArguments[0]]);
            f.Specific.ClassArguments = [malformed, f.Specific.ClassArguments[1]];
            f.Model.MethodInsts[1].ClassArguments = [malformed, f.Model.MethodInsts[1].ClassArguments[1]];
        }, "A generic argument with missing type arguments is not closed");
        Reject(f => f.Specific.ClassArguments = [f.Sigs.GenericParam(f.Enumerator.GenericParameters[0]), f.Specific.ClassArguments[1]], "Open specific context is rejected");
        Reject(f => f.Dispose.Flags |= MethodDef.Static, "Static ABI is rejected");
        Reject(f => f.Dispose.Parameters = [new ParamDef { Type = f.Sigs.Primitive(Il2CppTypeEnum.I4) }], "Extra managed arguments are rejected");
        Reject(f => f.Pointer(Fixture.Got, 0x7200), "Unknown metadata slot is rejected");
        Reject(f => Set(f.Image, "_relro", new List<(ulong, ulong)>()), "A writable GOT value is not treated as fixed metadata provenance");
        Reject(f => Set(f.Image, "_relro", new List<(ulong, ulong)> { (Fixture.Got, Fixture.Got + 4) }), "RELRO must cover the complete pointer width");
        Reject(f => f.Helpers.Add(Fixture.Rethrow, new HelperInfo(HelperKind.Rethrow, 1, false, false, "can return")), "Terminal Rethrow must independently be no-return");
    }

    private static void Frame()
    {
        var direct = new Fixture(); Check(direct.Run() && !direct.OriginalCall, "Direct sret starts a proved receiver lifetime");
        var copied = new Fixture(1, copied: true); Check(copied.Run() && !copied.OriginalCall, "A complete bounded sret copy is a separate receiver lifetime");
        var reused = new Fixture();
        Node old = reused.Add(reused.Entry, Op.Store, VT.None, reused.FrameAddress, reused.Const(7, VT.I32));
        reused.Entry.Nodes.Remove(old); reused.Entry.Nodes.Insert(reused.Entry.Nodes.IndexOf(reused.Initializer), old);
        Check(reused.Run(), "An earlier partial use of the same bytes is superseded by the paired full initialization");
        void Reject(Action<Fixture> alter, string why, int family = 0, bool copy = false, string? reasonContains = null)
        {
            var f = new Fixture(family, copy); alter(f); Check(!f.Run() && f.OriginalCall && f.Fn.Problems.Any(p => p.Contains("left native")) &&
                (reasonContains == null || f.Fn.Problems.Any(p => p.Contains(reasonContains))), why);
        }
        Reject(f => ((CallInfo)f.Initializer.Aux!).Target = 0x2500, "Unproved receiver construction is rejected");
        Reject(f => f.ZeroStore.Addr -= 4, "An old unrelated zero store does not start this paired lifetime");
        Reject(f => f.PendingStore.In[1] = f.Const(123), "An arbitrary pending pointer is not a caught managed exception");
        Reject(f => f.ReceiverStore.In[1] = f.Const(0), "A null or opaque receiver is not a constructed local");
        Reject(f =>
        {
            Node overlapping = f.Address(f.Entry, Fixture.FrameOffset + 8);
            f.Entry.Nodes.Remove(overlapping); f.Entry.Nodes.Insert(f.Entry.Nodes.IndexOf(f.Initializer), overlapping);
            f.ReceiverStore.In[1] = overlapping; f.Initializer.In[0] = overlapping;
        }, "The final receiver cannot overlap the pending-exception frame");
        Reject(f =>
        {
            Node copy = f.Entry.Nodes.First(n => n.Op == Op.Store && n.In[1].Op == Op.Load); copy.Dead = true;
        }, "A copy with a missing portion is rejected", 1, true);
        Reject(f =>
        {
            Node copy = f.Entry.Nodes.First(n => n.Op == Op.Store && n.In[1].Op == Op.Load);
            Node source = copy.In[1]; Node clobber = f.Add(f.Entry, Op.Store, VT.None, source.In[0], f.Const(99));
            f.Entry.Nodes.Remove(clobber); f.Entry.Nodes.Insert(f.Entry.Nodes.IndexOf(source), clobber);
        }, "A source overwritten before its load is rejected", 1, true);
        Reject(f =>
        {
            Node escape = f.Call(f.Body, 0x2500, Fixture.Caller + 0x52, [(0, f.FrameAddress)]); f.InBody(escape);
        }, "Passing the frame to an unknown call prevents expansion");
        Reject(f =>
        {
            Node store = f.Add(f.Entry, Op.Store, VT.None, f.Const(0xA100), f.Const(99));
            f.Entry.Nodes.Remove(store); f.Entry.Nodes.Insert(f.Entry.Nodes.IndexOf(f.ZeroStore), store);
        }, "Unknown-address writes after sret invalidate initialization proof");
        Reject(f =>
        {
            Node store = f.Add(f.Entry, Op.Store, VT.None, f.Const(0xA100), f.Const(99));
            f.Entry.Nodes.Remove(store); f.Entry.Nodes.Insert(f.Entry.Nodes.IndexOf(f.ZeroStore), store);
        }, "Unknown-address writes after the copy invalidate its destination proof", 1, true);
        Reject(f =>
        {
            Node low = f.Add(f.Body, Op.Trunc, VT.I32, f.FrameAddress);
            Node shifted = f.Add(f.Body, Op.ShrU, VT.I64, f.FrameAddress, f.Const(32, VT.I8));
            Node high = f.Add(f.Body, Op.Trunc, VT.I32, shifted);
            Node rebuilt = f.Add(f.Body, Op.Concat, VT.I64, high, low);
            Node[] bits = [low, shifted, high, rebuilt]; foreach (Node n in bits) f.Body.Nodes.Remove(n); f.Body.Nodes.InsertRange(0, bits);
            f.Body.Nodes.First(n => n.Op == Op.Call).In[0] = rebuilt;
        }, "Reassembling pointer bits across I32 nodes does not erase stack provenance");
        Reject(f =>
        {
            f.Helpers.Add(0x2400, new HelperInfo(HelperKind.SzArrayNew, 2, false, true, "fixture array allocation"));
            Node allocation = f.Call(f.Body, 0x2400, Fixture.Caller + 0x54, [(0, f.Const(0x7300)), (1, f.Const(1))]); f.InBody(allocation);
            Node array = f.Add(f.Body, Op.Proj, VT.I64, allocation); array.Imm = CallResult.IntReturn; f.InBody(array);
            Node element = f.Add(f.Body, Op.Add, VT.I64, array, f.Const(32)); f.InBody(element);
            Node adjacent = f.Address(f.Body, Fixture.FrameOffset - 8); f.InBody(adjacent);
            Node capture = f.Add(f.Body, Op.Store, VT.None, element, adjacent); capture.Addr = Fixture.Caller + 0x58; f.InBody(capture);
        }, "An adjacent stack pointer cannot escape and later be adjusted back into the frame", reasonContains: "address escapes");
        Reject(f =>
        {
            Node overwrite = f.Add(f.Body, Op.Store, VT.None, f.ReceiverStore.In[0], f.Const(99)); overwrite.Addr = Fixture.Caller + 0x52; f.InBody(overwrite);
            f.Body.Nodes.Remove(overwrite); f.Body.Nodes.Insert(0, overwrite);
            f.Body.Succs.Clear(); f.Join.Preds.Remove(f.Body); f.Body.Nodes.RemoveAll(n => n.IsTerminator); f.Add(f.Body, Op.Unreachable, VT.None);
        }, "A write in protected code is considered even when only the handler reaches cleanup");
        Reject(f =>
        {
            Node result = f.Add(f.Join, Op.Proj, VT.I64, f.CleanupCall); result.Imm = CallResult.IntReturn;
            f.Join.Nodes.Remove(result); f.Join.Nodes.Insert(1, result); f.Join.Nodes[^1].In = [result];
        }, "A live native result is never silently deleted");
    }

    private static void Exceptions()
    {
        var plain = new Fixture(); Check(plain.Run(), "An exact pad-zero call-site record permits propagation");
        var protectedCall = new Fixture(); protectedCall.ProtectedCall();
        Check(protectedCall.Run(), "A matching recovered managed catch permits expansion");
        Check(protectedCall.CleanupCall.Block!.Scope == 0 && protectedCall.CleanupCall.Block.Succs.All(b => b.Scope == 0), "Both expanded paths retain the original protected scope");
        void Reject(Action<Fixture> alter, string why)
        {
            var f = new Fixture(); alter(f); Check(!f.Run() && f.OriginalCall, why);
        }
        Reject(f => f.CallerTable.CallSites.RemoveAt(2), "A gap is not a pad-zero record");
        Reject(f => f.CallerTable.CallSites[2] = new(Fixture.Caller + 0x82, Fixture.Caller + 0x84, 0, 0), "The entire BL must be covered");
        Reject(f => f.CallerTable.CallSites[2] = new(Fixture.Caller + 0x80, Fixture.Caller + 0x84, Fixture.Caller + 0xE0, 3, 2, true), "Catch-all/terminate edges are not recast as ordinary propagation");
        Reject(f => f.CallerTable.CallSites[2] = new(Fixture.Caller + 0x80, Fixture.Caller + 0x84, Fixture.Caller + 0xE0, 0), "Cleanup-only landing pads need their own representation");
        Reject(f => f.Tables[Fixture.Caller] = null, "Missing caller LSDA proof keeps the call opaque");
        Reject(f => { f.ProtectedCall(); f.Fn.TryRegions[0].Funclet = Fixture.Caller + 0x70; }, "An unrelated recovered catch is not the original edge");
        var missing = new Fixture();
        missing.Word(Fixture.Caller + 0xA0, Fixture.Bl(Fixture.Caller + 0xA0, missing.Helper));
        missing.CallerTable.CallSites.Add(new(Fixture.Caller + 0xA0, Fixture.Caller + 0xA4, Fixture.Caller + 0xE0, 3, 2, true));
        Check(missing.Run() && missing.Fn.Problems.Any(p => p.Contains("0x30A0") && p.Contains("not represented by the lifter")), "A raw catch-all helper omitted by the lifter receives an honest diagnostic");
    }

    private static void Order()
    {
        for (int family = 0; family < 2; family++)
        {
            var f = new Fixture(family, copied: family != 0); Check(f.Run(), "The order fixture must actually expand");
            List<Node> nodes = f.CleanupCall.Block!.Nodes;
            Node pending = nodes[nodes.IndexOf(f.CleanupCall) + 1];
            Check(pending.Op == Op.Load && ReferenceEquals(pending.In[0], f.FrameAddress), "The pending load is after Dispose and keeps the original frame address");
            Block throwing = f.CleanupCall.Block.Succs[0];
            Check(throwing.Succs.Count == 0 && throwing.Terminator?.Op == Op.Unreachable &&
                throwing.Nodes.Any(n => n.Aux is CallInfo { NoReturn: true } && ReferenceEquals(n.In.Single(), pending)), "The nonnull branch rethrows that exact load and has no normal successor");
            Check(((CallInfo)f.CleanupCall.Aux!).Target == f.CleanupTarget && f.CleanupCall.In[1].Op == Op.SlotValue &&
                (ulong)f.CleanupCall.In[1].Imm == f.Slot, "The exact native managed target and specific MethodInfo are retained");
            var normal = Execute(f, caught: false); Check(normal.Outcome == "return" && normal.Events.IndexOf("dispose") < normal.Events.IndexOf("pending-read"), "Null pending: Dispose then read then normal continuation");
            var original = Execute(f, caught: true); Check(original.Outcome == "rethrow:49153", "Nonnull pending: rethrow the original exception identity");
            var aliased = Execute(f, caught: true, newPending: 0xC002); Check(aliased.Outcome == "rethrow:49154", "A Dispose-side alias write is observed by the later load");
            var cleared = Execute(f, caught: true, newPending: 0); Check(cleared.Outcome == "return", "Dispose may clear the aliased pending slot before it is read");
            var threw = Execute(f, caught: true, disposeThrows: true); Check(threw.Outcome == "dispose-threw" && !threw.Events.Contains("pending-read"), "A throwing Dispose never reads or substitutes the saved exception");
        }
    }

    private static (string Outcome, List<string> Events) Execute(Fixture f, bool caught, long? newPending = null, bool disposeThrows = false)
    {
        const long sp = 0x100000, wrapper = 0xB000;
        var memory = new Dictionary<long, long> { [wrapper] = 0xC001 };
        var values = new Dictionary<Node, long>();
        var events = new List<string>();
        long Value(Node n)
        {
            if (values.TryGetValue(n, out long value)) return value;
            value = n.Op switch
            {
                Op.Const or Op.SlotValue => n.Imm,
                Op.Param when ReferenceEquals(n, f.Sp) => sp,
                Op.Add => Value(n.In[0]) + Value(n.In[1]),
                Op.CmpNe => Value(n.In[0]) != Value(n.In[1]) ? 1 : 0,
                Op.Idiom when n.Imm == (long)IdiomKind.TryEntry => caught ? 1 : 0,
                Op.Idiom when n.Imm == (long)IdiomKind.CaughtWrapper => wrapper,
                _ => throw new InvalidOperationException("Unexpected lazy value " + n.Op)
            };
            values[n] = value; return value;
        }
        Block block = f.Fn.Entry;
        for (int budget = 0; budget < 32; budget++)
        {
            Block? next = null;
            foreach (Node n in block.Nodes)
            {
                switch (n.Op)
                {
                    case Op.Load:
                    {
                        long address = Value(n.In[0]);
                        if (address == sp + Fixture.FrameOffset && events.Contains("dispose")) events.Add("pending-read");
                        values[n] = memory.GetValueOrDefault(address); break;
                    }
                    case Op.Store: memory[Value(n.In[0])] = Value(n.In[1]); break;
                    case Op.Call:
                    {
                        var info = (CallInfo)n.Aux!;
                        if (info.Target == Fixture.InitTarget)
                        {
                            int input = info.Slots.FindIndex(s => s == new ArgSlot(ArgSlotKind.IntReg, 8));
                            for (int i = 0; i < f.ReceiverSize; i += 8) memory[Value(n.In[input]) + i] = 0;
                        }
                        else if (info.Target == f.CleanupTarget)
                        {
                            Check(Value(n.In[0]) == sp + Fixture.ReceiverOffset && Value(n.In[1]) == (long)f.Slot, "Interpreter sees the actual receiver and exact descriptor");
                            events.Add("dispose");
                            if (disposeThrows) return ("dispose-threw", events);
                            if (newPending != null) memory[sp + Fixture.FrameOffset] = newPending.Value;
                        }
                        else if (info.Target == Fixture.Rethrow) return ("rethrow:" + Value(n.In[0]), events);
                        else if (info.Target != Fixture.MoveTarget) throw new InvalidOperationException("Unexpected call target");
                        break;
                    }
                    case Op.Branch: next = block.Succs[Value(n.In[0]) != 0 ? 0 : 1]; break;
                    case Op.Jump: next = block.Succs.Single(); break;
                    case Op.Return: return ("return", events);
                    case Op.Unreachable: throw new InvalidOperationException("A no-return branch unexpectedly continued");
                }
            }
            block = next ?? throw new InvalidOperationException("No continuation");
        }
        throw new InvalidOperationException("Fixture did not terminate");
    }
}
