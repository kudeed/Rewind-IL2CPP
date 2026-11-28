using System.Diagnostics;
using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Abi;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Recover;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;
using HostRuntime = System.Runtime.CompilerServices.RuntimeHelpers;
using Helpers = Rewind.Analysis.Runtime.RuntimeHelpers;

// Exercises the actual private effect callbacks and the existing byte-range splitter. No lifter, HIR builder,
// native recovery, Unity or historical test suite is invoked. The memory oracle only interprets this fixture's IR.
internal static class Program
{
    private const BindingFlags All = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
    private const ulong SinF = 0x1000, SinD = 0x1010, UnknownKind = 0x1020, UnknownTarget = 0x1030;
    private const int Reused = -176, SineAt = -340, CosineAt = -344;
    private static int assertions;
    private static readonly List<object> results = [];
    private static readonly string RunId = Guid.NewGuid().ToString("N");
    private static string? journal;

    private sealed record AbiCase(RegisterModel Registers, int Sine, int Cosine);
    // Literal ABI expectations, independent of the production SharedPositions expression.
    private static readonly AbiCase[] Abis = [new(RegisterModel.Arm64, 0, 1), new(RegisterModel.Win64, 1, 2)];
    private static readonly MethodInfo Extent = typeof(MethodPipeline).GetMethod("EscapeExtent", All, null,
        [typeof(Node), typeof(int), typeof(bool).MakeByRefType()], null)!;
    private static readonly MethodInfo Writes = typeof(MethodPipeline).GetMethod("WritesOnly", All, null, [typeof(Node), typeof(int)], null)!;
    private static readonly MethodInfo Reads = typeof(MethodPipeline).GetMethod("ReadsOnly", All)!;
    private static readonly MethodInfo Removable = typeof(MethodPipeline).GetMethod("WritesAndNothingElse", All)!;

    private static int Main(string[] args)
    {
        if (args.SequenceEqual(["--guard-child"])) return GuardChild();
        string? report = null;
        var selected = new HashSet<string>(StringComparer.Ordinal);
        for (int i = 0; i < args.Length; i++)
        {
            if (args[i] is not ("--group" or "--report" or "--journal") || i + 1 >= args.Length)
                throw new ArgumentException("Usage: sincos-effects [--group effects,stack,cfg,aliases,reject,disabled] [--report file] [--journal jsonl]");
            string option = args[i], value = args[++i];
            if (option == "--group") selected.UnionWith(value.Split(',', StringSplitOptions.RemoveEmptyEntries));
            else if (option == "--report") report = value;
            else journal = value;
        }
        journal ??= report == null ? null : report + ".groups.jsonl";
        var groups = new (string Id, Action Run)[]
        {
            ("effects", EffectMap), ("stack", StackLifetime), ("cfg", BranchLifetimes),
            ("aliases", OutputAliases), ("reject", ConservativeBoundaries), ("disabled", DisabledGate)
        };
        if (selected.Except(groups.Select(g => g.Id)).Any()) throw new ArgumentException("Unknown --group name");
        if (Environment.GetEnvironmentVariable("REWIND_NO_HELPER_EXTENTS") != null)
            throw new InvalidOperationException("Run the normal suite with REWIND_NO_HELPER_EXTENTS unset; the disabled group checks it in an isolated child.");
        bool failed = false;
        foreach (var group in groups)
        {
            if (selected.Count != 0 && !selected.Contains(group.Id)) continue;
            int before = assertions;
            string? error = null;
            try { group.Run(); }
            catch (Exception ex) { error = ex.ToString(); failed = true; }
            var result = new { run_id = RunId, group = group.Id, status = error == null ? "pass" : "fail", assertions = assertions - before, error };
            results.Add(result);
            string line = JsonSerializer.Serialize(result);
            Console.WriteLine(line);
            if (journal != null) File.AppendAllText(journal, line + Environment.NewLine);
        }
        var summary = new
        {
            suite = "sincos-output-effects", run_id = RunId, assertions, groups = results,
            analysis_binary_sha256 = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(typeof(MethodPipeline).Assembly.Location))),
            scope = "Only SinCos effect/stack fixtures; no historical suites, Unity, or native recovery. Group journal appends across retries."
        };
        string json = JsonSerializer.Serialize(summary, new JsonSerializerOptions { WriteIndented = true });
        Console.WriteLine(json);
        if (report != null) File.WriteAllText(report, json + Environment.NewLine);
        return failed ? 1 : 0;
    }

    private static void Check(bool condition, string message)
    {
        assertions++;
        if (!condition) throw new InvalidOperationException(message);
    }
    private static void Set(object owner, string name, object value) => owner.GetType().GetField(name, All)!.SetValue(owner, value);
    private static void Backing(object owner, string name, object value) => Set(owner, "<" + name + ">k__BackingField", value);
    private static object Invoke(MethodInfo method, object owner, params object?[] args)
    {
        try { return method.Invoke(owner, args)!; }
        catch (TargetInvocationException ex) when (ex.InnerException != null)
        {
            System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(ex.InnerException).Throw();
            throw;
        }
    }
    private sealed class Image : NativeImage
    {
        public override ImageFormat Format => Arch == CpuArch.Arm64 ? ImageFormat.Elf : ImageFormat.PE;
        public Image(CpuArch arch)
        {
            Arch = arch; PointerSize = 8; MemoryBase = 0; Memory = new byte[16];
        }
    }

    private sealed class Effects
    {
        public MethodPipeline Pipeline { get; }
        public AbiCase Abi { get; }
        public Effects(AbiCase abi)
        {
            Abi = abi;
            var model = (Il2CppModel)HostRuntime.GetUninitializedObject(typeof(Il2CppModel));
            Backing(model, "Image", new Image(abi.Registers == RegisterModel.Arm64 ? CpuArch.Arm64 : CpuArch.X64));
            Backing(model, "Sigs", new SigFactory());
            Backing(model, "MethodsByAddress", new Dictionary<ulong, List<MethodDef>>());
            Backing(model, "InstsByAddress", new Dictionary<ulong, List<MethodInst>>());
            var helpers = new Helpers();
            helpers.Add(SinF, Helpers.Classify("sincosf")!);
            helpers.Add(SinD, Helpers.Classify("sincos")!);
            helpers.Add(UnknownKind, new HelperInfo(HelperKind.None, 0, false, false, "unclassified"));
            var layouts = new LayoutCalculator(model);
            var analysis = (ProgramAnalysis)HostRuntime.GetUninitializedObject(typeof(ProgramAnalysis));
            Backing(analysis, "Model", model); Backing(analysis, "Helpers", helpers); Backing(analysis, "Layouts", layouts);
            Backing(analysis, "Abi", abi.Registers == RegisterModel.Arm64 ? (CallingConvention)new Aapcs64Abi(model, layouts) : new Win64Abi(model, layouts));
            // A cached empty resolution exercises the real unknown-target callback without loading an ELF or
            // probing code. Both method tables, the exact-copy index and its target cache are initialized.
            var copies = new CopyMatcher.Result(); copies.Copies[UnknownTarget] = [];
            Backing(analysis, "ExactCopies", copies);
            Set(analysis, "_copyTargets", new Dictionary<ulong, CallTarget> { [UnknownTarget] = new() });
            Pipeline = (MethodPipeline)HostRuntime.GetUninitializedObject(typeof(MethodPipeline));
            Set(Pipeline, "_program", analysis);
        }
        public int Size(Node call, int input) => (int)Invoke(Extent, Pipeline, call, input, false);
        public bool Write(Node call, int input) => (bool)Invoke(Writes, Pipeline, call, input);
        public bool Read(Node call, int input) => (bool)Invoke(Reads, Pipeline, call, input);
        public bool CanRemove(Node call, int input) => (bool)Invoke(Removable, Pipeline, call, input);

        public Node Call(bool wide, Node sine, Node cosine, bool reverse = false, ulong target = 0)
        {
            var pieces = new List<(ArgSlot Slot, Node Value)>
            {
                (new(ArgSlotKind.FloatReg, 0), new() { Op = Op.Const, Type = VT.I32, Imm = wide ? 0 : 0x3f000000 }),
                (new(ArgSlotKind.IntReg, Abi.Sine), sine), (new(ArgSlotKind.IntReg, Abi.Cosine), cosine)
            };
            if (wide) pieces.Add((new(ArgSlotKind.FloatReg, 1), new() { Op = Op.Const, Type = VT.I32, Imm = 0x3fe00000 }));
            if (reverse) pieces.Reverse();
            return new Node { Op = Op.Call, Type = VT.None, In = pieces.Select(p => p.Value).ToArray(),
                Aux = new CallInfo { Target = target != 0 ? target : wide ? SinD : SinF, Slots = pieces.Select(p => p.Slot).ToList() } };
        }
        public int Output(Node call, bool cosine = false) => ((CallInfo)call.Aux!).Slots.FindIndex(s =>
            s.Kind == ArgSlotKind.IntReg && s.Index == (cosine ? Abi.Cosine : Abi.Sine));
    }

    private static Node Param() => new() { Op = Op.Param, Type = VT.I64 };
    private static Node Address(Node root, long offset) => offset == 0 ? root : new()
    {
        Op = Op.Add, Type = VT.I64, In = [root, new() { Op = Op.Const, Type = VT.I64, Imm = offset }]
    };

    private static void EffectMap()
    {
        foreach (AbiCase abi in Abis)
            foreach (bool wide in new[] { false, true })
                foreach (bool reversed in new[] { false, true })
                {
                    var effects = new Effects(abi); Node baseNode = Param(); int bytes = wide ? 8 : 4;
                    Node call = effects.Call(wide, Address(baseNode, -128), Address(baseNode, -128 + bytes), reversed);
                    foreach (bool cosine in new[] { false, true })
                    {
                        int input = effects.Output(call, cosine);
                        Check(effects.Size(call, input) == bytes, abi.Registers.Name + " exact output extent");
                        Check(effects.Write(call, input), "adjacent non-overlapping outputs are write-only");
                        Check(!effects.Read(call, input), "outputs are not read-only");
                        Check(!effects.CanRemove(call, input), "an unused output does not make the native call removable");
                    }
                    int floating = ((CallInfo)call.Aux!).Slots.FindIndex(s => s.Kind == ArgSlotKind.FloatReg);
                    Check(effects.Size(call, floating) < 0 && !effects.Write(call, floating), "float input is no output pointer");
                }
    }

    private sealed class StackFixture
    {
        public readonly Function Function;
        public readonly Effects Effects;
        public readonly Node OldRead, NewRead, Helper;
        public readonly Node? JoinRead;
        public readonly List<Node> OldStores = [], NewStores = [];
        private readonly Dictionary<Node, int> readers = [];
        private readonly Node sp;
        public StackFixture(bool branch = false, bool partial = false, bool realJoinRead = false, bool wide = false,
            int aliasShift = int.MaxValue, bool unusedOutputs = false)
        {
            Effects = new Effects(Abis[0]); Function = new Function { Regs = RegisterModel.Arm64, Address = 0x5000 };
            var entry = new Block { Id = 0 }; Function.Blocks.Add(entry);
            var ir = new IrBuilder(Function) { Current = entry };
            sp = Function.NewNode(Op.Param, VT.I64, null); Function.Params[Function.Regs.StackPointer] = sp;
            Node At(int offset) => ir.Add(sp, ir.Const(VT.I64, offset));
            Node Store(int at, VT type, long value) => ir.Raw(Op.Store, VT.None, At(at), ir.Const(type, value));
            Node Reader(int size)
            {
                Node n = ir.Raw(Op.Call, VT.None, At(Reused)); n.Aux = new CallInfo(); readers[n] = size; return n;
            }
            OldStores.Add(Store(Reused, VT.I64, 0x2222222211111111));
            OldStores.Add(Store(Reused + 8, VT.I64, 0x4444444433333333));
            OldRead = Reader(16);
            Block? join = null;
            if (branch)
            {
                var fresh = new Block { Id = 1 }; var bypass = new Block { Id = 2 }; join = new Block { Id = 3 };
                Function.Blocks.AddRange([fresh, bypass, join]);
                ir.Raw(Op.Branch, VT.None, ir.Const(VT.I1, 1));
                entry.Succs.AddRange([fresh, bypass]); fresh.Preds.Add(entry); bypass.Preds.Add(entry);
                fresh.Succs.Add(join); bypass.Succs.Add(join); join.Preds.AddRange([fresh, bypass]);
                ir.Current = bypass; ir.Raw(Op.Jump, VT.None);
                ir.Current = fresh;
            }
            NewStores.Add(Store(Reused, VT.I64, 0));
            if (!partial) NewStores.Add(Store(Reused + 8, VT.I32, 0x3f123456));
            NewRead = Reader(12);
            if (join != null) { ir.Raw(Op.Jump, VT.None); ir.Current = join; }
            if (realJoinRead) JoinRead = Reader(16);
            int bytes = wide ? 8 : 4;
            int sine = wide ? -336 : SineAt;
            int cosine = aliasShift == int.MaxValue ? sine - bytes : sine + aliasShift;
            Helper = Effects.Call(wide, At(sine), At(cosine));
            Helper.Block = ir.Current; Helper.Id = Function.NextId++; ir.Current.Nodes.Add(Helper);
            if (!unusedOutputs)
            {
                ir.Raw(Op.Load, VTExtensions.IntOfBytes(bytes), At(sine));
                ir.Raw(Op.Load, VTExtensions.IntOfBytes(bytes), At(cosine));
            }
            ir.Raw(Op.Return, VT.None);
        }
        public int Split(bool oldUnbounded = false, bool includeOutputs = false) => StackSplitting.Run(Function,
            includeOutputs ? [Reused, Offset(Helper.In[Effects.Output(Helper)])] : [Reused],
            (call, input) => readers.TryGetValue(call, out int bytes) ? bytes : oldUnbounded ? -1 : Effects.Size(call, input),
            (call, input) => !readers.ContainsKey(call) && !oldUnbounded && Effects.Write(call, input),
            (call, _) => readers.ContainsKey(call),
            (call, input) => !readers.ContainsKey(call) && Effects.CanRemove(call, input));
        public static int Offset(Node address) => address.Op == Op.Add ? checked((int)IrBuilder.SImm(address.In[1])) : 0;
        public bool Separated => Offset(OldRead.In[0]) != Offset(NewRead.In[0]);

        public string Observe(bool takeNew = true)
        {
            var memory = new Dictionary<int, byte>(); var seen = new List<string>();
            ulong Value(Node n) => n.Op == Op.Const ? n.UImm : throw new InvalidOperationException("Fixture only writes literal values");
            void Write(int at, int count, ulong value)
            {
                for (int i = 0; i < count; i++) memory[at + i] = (byte)(value >> (8 * i));
            }
            string Read(int at, int count) => Convert.ToHexString(Enumerable.Range(at, count).Select(i => memory.GetValueOrDefault(i)).ToArray());
            Block? block = Function.Entry;
            while (block != null)
            {
                foreach (Node n in block.Nodes)
                {
                    if (n.Dead) continue;
                    if (n.Op == Op.Store) Write(Offset(n.In[0]), n.In[1].Type.Bytes(), Value(n.In[1]));
                    else if (readers.TryGetValue(n, out int bytes)) seen.Add("read:" + Read(Offset(n.In[0]), bytes));
                    else if (ReferenceEquals(n, Helper))
                    {
                        // Two opaque distinct output patterns: checks relocation, ordering and alias identity,
                        // without treating System.Math as an oracle for the C library's sincos implementation.
                        int width = ((CallInfo)n.Aux!).Target == SinD ? 8 : 4;
                        Write(Offset(n.In[Effects.Output(n)]), width, 0x0123456789abcdef);
                        Write(Offset(n.In[Effects.Output(n, true)]), width, 0xfedcba9876543210);
                        seen.Add("helper");
                    }
                    else if (n.Op == Op.Load) seen.Add("load:" + Read(Offset(n.In[0]), n.Type.Bytes()));
                }
                block = block.Succs.Count switch { 0 => null, 1 => block.Succs[0], 2 => block.Succs[takeNew ? 0 : 1], _ => throw new InvalidOperationException() };
            }
            return string.Join("|", seen);
        }
        public void CheckPairing()
        {
            foreach (Node store in OldStores) Check(Offset(store.In[0]) >= Offset(OldRead.In[0]) &&
                Offset(store.In[0]) + store.In[1].Type.Bytes() <= Offset(OldRead.In[0]) + 16, "old consumer retains its exact stores");
            foreach (Node store in NewStores) Check(Offset(store.In[0]) >= Offset(NewRead.In[0]) &&
                Offset(store.In[0]) + store.In[1].Type.Bytes() <= Offset(NewRead.In[0]) + 12, "new consumer retains its exact stores");
            Check(!Helper.Dead && Helper.Block!.Nodes.Contains(Helper), "native helper call remains ordered and present");
        }
    }

    private static void StackLifetime()
    {
        var old = new StackFixture(); string oldValues = old.Observe(); old.Split(oldUnbounded: true);
        Check(!old.Separated, "the old unknown-extent callback reproduces the false shared lifetime");
        Check(old.Observe() == oldValues, "baseline fixture observations are stable");
        foreach (bool wide in new[] { false, true })
        {
            var f = new StackFixture(wide: wide); string before = f.Observe();
            Check(f.Split() > 0 && f.Separated, "precise outputs allow the 16-byte and 12-byte lifetimes to separate");
            Check(f.Observe() == before, "all real byte observations and helper order survive separation");
            f.CheckPairing();
        }
    }
    private static void BranchLifetimes()
    {
        foreach (bool realRead in new[] { false, true })
        {
            var f = new StackFixture(branch: true, realJoinRead: realRead);
            string yes = f.Observe(), no = f.Observe(false); f.Split();
            Check(f.Separated != realRead, realRead ? "real 16-byte join read keeps both lifetimes connected" : "unrelated outputs do not connect branch lifetimes");
            Check(f.Observe() == yes && f.Observe(false) == no, "both CFG paths retain their original byte observations");
            f.CheckPairing();
        }
        var partial = new StackFixture(partial: true); string partialBefore = partial.Observe(); partial.Split();
        Check(!partial.Separated, "a real read of the old third component prevents a partial-overwrite split");
        Check(partial.Observe() == partialBefore, "partial overwrite keeps the old component");
    }
    private static void OutputAliases()
    {
        foreach (AbiCase abi in Abis)
            foreach (bool wide in new[] { false, true })
                foreach (int shift in wide ? new[] { 0, 2, -2, 4, -4, 6 } : new[] { 0, 2, -2 })
                {
                    var e = new Effects(abi); Node root = Param(); int bytes = wide ? 8 : 4;
                    Node call = e.Call(wide, Address(root, -64), Address(root, -64 + shift));
                    foreach (bool cosine in new[] { false, true })
                    {
                        int i = e.Output(call, cosine);
                        Check(e.Size(call, i) == bytes && !e.Write(call, i), "same/overlapping outputs keep exact bounds and conservative reads");
                    }
                }
        foreach (bool wide in new[] { false, true })
            foreach (int shift in wide ? new[] { 0, 2, -2, 4, -4, 6 } : new[] { 0, 2, -2 })
            {
                var f = new StackFixture(wide: wide, aliasShift: shift);
                int first = StackFixture.Offset(f.Helper.In[f.Effects.Output(f.Helper)]);
                int second = StackFixture.Offset(f.Helper.In[f.Effects.Output(f.Helper, true)]);
                string before = f.Observe(); f.Split(includeOutputs: true);
                Check(StackFixture.Offset(f.Helper.In[f.Effects.Output(f.Helper)]) == first &&
                    StackFixture.Offset(f.Helper.In[f.Effects.Output(f.Helper, true)]) == second, "aliased outputs are not individually redirected");
                Check(f.Observe() == before, "overlapping output byte results remain identical");
            }
        var unknown = new Effects(Abis[0]);
        Node separateNames = unknown.Call(false, Param(), Param());
        Check(unknown.Size(separateNames, unknown.Output(separateNames)) == 4 && !unknown.Write(separateNames, unknown.Output(separateNames)),
            "different SSA variables do not prove pointer non-aliasing");
        foreach (long farOffset in new[] { -0x4000000L, 0x4000000L, long.MinValue, long.MaxValue })
        {
            Node root = Param(); Node far = unknown.Call(false, Address(root, farOffset), root);
            Check(unknown.Size(far, unknown.Output(far)) == 4 && !unknown.Write(far, unknown.Output(far)),
                "offsets outside the proof bound stay conservative without subtraction overflow");
        }
        var unused = new StackFixture(unusedOutputs: true); unused.Split(includeOutputs: true);
        Check(!unused.Helper.Dead && unused.Helper.Block!.Nodes.Contains(unused.Helper), "both unused results do not delete sincos effects");
    }
    private static void ConservativeBoundaries()
    {
        foreach (AbiCase abi in Abis)
        {
            var e = new Effects(abi);
            Node Fresh() { Node root = Param(); return e.Call(false, Address(root, -64), Address(root, -60)); }
            void Reject(string reason, Action<Node, CallInfo> change)
            {
                Node call = Fresh(); var info = (CallInfo)call.Aux!; change(call, info);
                for (int i = 0; i < call.In.Length; i++) Check(e.Size(call, i) < 0 && !e.Write(call, i), reason);
            }
            Reject("unknown helper remains unbounded", (_, i) => i.Target = UnknownKind);
            Reject("unknown target remains unbounded", (_, i) => i.Target = UnknownTarget);
            Reject("indirect call cannot borrow the direct target's effect", (_, i) => i.Indirect = true);
            Reject("intrinsic does not borrow the direct target's effect", (_, i) => i.Intrinsic = "unclassified_intrinsic");
            Reject("mismatched input/slot lengths", (n, _) => n.In = n.In[..^1]);
            Reject("extra unlabelled input", (n, _) => n.In = [.. n.In, Param()]);
            Reject("duplicate sine slot", (n, i) => { i.Slots.Add(new(ArgSlotKind.IntReg, abi.Sine)); n.In = [.. n.In, Param()]; });
            Reject("duplicate cosine slot", (n, i) => { i.Slots.Add(new(ArgSlotKind.IntReg, abi.Cosine)); n.In = [.. n.In, Param()]; });
            Reject("missing peer output", (n, i) => { int at = e.Output(n, true); i.Slots.RemoveAt(at); n.In = n.In.Where((_, k) => k != at).ToArray(); });
            Reject("non-pointer-width output input", (n, _) => n.In[e.Output(n, true)] = new() { Op = Op.Const, Type = VT.I32 });
            Node bounded = Fresh(); var slots = (CallInfo)bounded.Aux!;
            slots.Slots.Add(new(ArgSlotKind.IntReg, 7)); bounded.In = [.. bounded.In, Param()];
            Check(e.Size(bounded, bounded.In.Length - 1) < 0 && !e.Write(bounded, bounded.In.Length - 1), "unrelated integer register is not an output");
            slots.Slots[^1] = new(ArgSlotKind.Stack, 0);
            Check(e.Size(bounded, bounded.In.Length - 1) < 0 && !e.Write(bounded, bounded.In.Length - 1), "stack slot is not a register output");
            Check(e.Size(bounded, -1) < 0 && !e.Write(bounded, -1), "negative input index is conservative");
            Check(e.Size(bounded, bounded.In.Length) < 0 && !e.Write(bounded, bounded.In.Length), "past-end input index is conservative");
        }
    }
    private static int GuardChild()
    {
        try
        {
            Check(Environment.GetEnvironmentVariable("REWIND_NO_HELPER_EXTENTS") != null, "child guard set before type initialization");
            foreach (AbiCase abi in Abis)
                foreach (bool wide in new[] { false, true })
                {
                    var e = new Effects(abi); Node root = Param(); Node call = e.Call(wide, Address(root, -64), Address(root, -48));
                    foreach (bool cosine in new[] { false, true })
                    {
                        int i = e.Output(call, cosine);
                        Check(e.Size(call, i) < 0 && !e.Write(call, i), "NoHelperExtents disables both effect claims");
                    }
                }
            Console.WriteLine(JsonSerializer.Serialize(new { disabled_child = true, assertions }));
            return 0;
        }
        catch (Exception e) { Console.Error.WriteLine(e); return 1; }
    }
    private static void DisabledGate()
    {
        string executable = Environment.ProcessPath ?? throw new InvalidOperationException("No current process executable");
        var start = new ProcessStartInfo(executable) { UseShellExecute = false, RedirectStandardOutput = true, RedirectStandardError = true };
        if (Path.GetFileNameWithoutExtension(executable).Equals("dotnet", StringComparison.OrdinalIgnoreCase))
            start.ArgumentList.Add(typeof(Program).Assembly.Location);
        start.ArgumentList.Add("--guard-child"); start.Environment["REWIND_NO_HELPER_EXTENTS"] = "1";
        using Process child = Process.Start(start) ?? throw new InvalidOperationException("Could not start disabled-gate child");
        Task<string> output = child.StandardOutput.ReadToEndAsync(), error = child.StandardError.ReadToEndAsync();
        if (!child.WaitForExit(30000)) { child.Kill(); throw new TimeoutException("Disabled-gate child exceeded 30 seconds"); }
        string stdout = output.GetAwaiter().GetResult(), stderr = error.GetAwaiter().GetResult();
        Check(child.ExitCode == 0, "isolated disabled-gate result: " + stderr);
        using JsonDocument result = JsonDocument.Parse(stdout);
        Check(result.RootElement.GetProperty("disabled_child").GetBoolean(), "disabled guard actually ran");
        assertions += result.RootElement.GetProperty("assertions").GetInt32();
    }
}
