using System.Collections;
using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Model;
using Rewind.Runtime;
using Helpers = Rewind.Analysis.Runtime.RuntimeHelpers;

internal static class Program
{
    private const BindingFlags All = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
    private static readonly Type SVal = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.SVal")!;
    private static int assertions;

    private static string Hash(string path) => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));
    private static int Main(string[] args)
    {
        string? journal = null, report = null;
        string group = "dominating-receiver";
        for (int i = 0; i < args.Length; i += 2)
        {
            if (i + 1 == args.Length) throw new ArgumentException("Missing option value");
            switch (args[i])
            {
                case "--group": group = args[i + 1]; break;
                case "--journal": journal = args[i + 1]; break;
                case "--report": report = args[i + 1]; break;
                default: throw new ArgumentException("Use --group dominating-receiver --journal file.jsonl --report file.json");
            }
        }
        if (group != "dominating-receiver" || journal == null)
            throw new ArgumentException("Only the new dominating-receiver group exists; --journal is required.");
        var identity = new
        {
            fixture_sha256 = Hash(typeof(Program).Assembly.Location),
            analysis_sha256 = Hash(typeof(HirBuilder).Assembly.Location),
            core_sha256 = Hash(typeof(Il2CppModel).Assembly.Location)
        };
        string key = Convert.ToHexStringLower(SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(JsonSerializer.Serialize(identity))));
        bool passed = false;
        if (File.Exists(journal))
            foreach (string line in File.ReadLines(journal))
            {
                if (string.IsNullOrWhiteSpace(line)) continue;
                using JsonDocument doc = JsonDocument.Parse(line);
                JsonElement root = doc.RootElement;
                if (root.GetProperty("identity_key").GetString() == key && root.GetProperty("group").GetString() == group &&
                    root.GetProperty("status").GetString() == "pass") passed = true;
            }
        string? error = null;
        if (!passed)
            try { DominatingReceiver(); }
            catch (Exception e) { error = e.ToString(); }
        var row = new
        {
            identity_key = key, group, status = passed ? "skip-pass" : error == null ? "pass" : "fail",
            assertions, error, utc = DateTime.UtcNow.ToString("O")
        };
        string json = JsonSerializer.Serialize(row);
        File.AppendAllText(journal, json + Environment.NewLine);
        Console.WriteLine(json);
        var summary = new
        {
            suite = "receiver-precedence-r25-followup", identity, identity_key = key, assertions, groups = new[] { row },
            scope = "Only the new dominating type-fact receiver precedence delta. No original receiver groups, native recovery, exports or Unity."
        };
        string output = JsonSerializer.Serialize(summary, new JsonSerializerOptions { WriteIndented = true });
        Console.WriteLine(output);
        if (report != null) File.WriteAllText(report, output + Environment.NewLine);
        return error == null ? 0 : 1;
    }

    private static void Check(bool condition, string why)
    {
        assertions++;
        if (!condition) throw new InvalidOperationException(why);
    }
    private static object? Get(object obj, string name) => obj.GetType().GetField(name, All)!.GetValue(obj);
    private static void Set(object obj, string name, object value) => obj.GetType().GetField(name, All)!.SetValue(obj, value);

    private sealed class Image : NativeImage
    {
        public override ImageFormat Format => ImageFormat.Elf;
        public Image()
        {
            Arch = CpuArch.Arm64; PointerSize = 8; MemoryBase = 0x1000; Memory = new byte[0x1000];
            Sections.Add(new ImageSection("il2cpp", MemoryBase, (ulong)Memory.Length, SectionFlags.Read | SectionFlags.Execute));
            Code(0x1100, 0xf9400808, 0xd65f03c0); // ldr x8,[x0,#16]; ret: the target really reads this
            Code(0x1200, 0xd65f03c0);
        }
        private void Code(ulong at, params uint[] words)
        {
            for (int i = 0; i < words.Length; i++)
                System.Buffers.Binary.BinaryPrimitives.WriteUInt32LittleEndian(Memory.AsSpan(checked((int)(at - MemoryBase)) + 4 * i), words[i]);
            FunctionTable.Add(new FunctionRange(at, at + (ulong)(4 * words.Length), 0));
        }
    }

    private sealed class Fixture
    {
        public readonly Il2CppModel Model;
        public readonly AssemblyModel Assembly;
        public readonly TypeDef Task, Parent, Other, Container;
        public readonly MethodDef AddChild, Caller;
        public readonly ProgramAnalysis Analysis;
        public TypeSig Int => Model.Sigs.Primitive(Il2CppTypeEnum.I4);

        public Fixture()
        {
            var image = new Image();
            var metadata = (MetadataFile)typeof(MetadataFile).GetConstructor(All, null,
                [typeof(byte[]), typeof(int), typeof(int)], null)!.Invoke([new byte[32], 39, 3900]);
            var binary = (Il2CppBinary)typeof(Il2CppBinary).GetConstructor(All, null,
                [typeof(NativeImage), typeof(int)], null)!.Invoke([image, 3900]);
            Model = new Il2CppModel(image, metadata, binary);
            Assembly = new AssemblyModel { Name = "ReceiverPrecedenceFixture", ImageName = "ReceiverPrecedenceFixture.dll" };
            Model.Assemblies = [Assembly];
            Task = Type("Task", Model.Sigs.Primitive(Il2CppTypeEnum.Object));
            Parent = Type("ParentTask", Task.Sig);
            Other = Type("OtherTask", Task.Sig);
            Container = Type("Loader", Model.Sigs.Primitive(Il2CppTypeEnum.Object));
            AddChild = Method(Parent, "AddChild", 0x1100, false,
                new ParamDef { Name = "child", Type = Task.Sig }, new ParamDef { Name = "index", Type = Int });
            Caller = Method(Container, "Load", 0x1200, true,
                new ParamDef { Name = "parent", Type = Task.Sig }, new ParamDef { Name = "child", Type = Task.Sig },
                new ParamDef { Name = "index", Type = Int });
            Analysis = new ProgramAnalysis(Model, new Helpers());
        }

        private TypeDef Type(string name, TypeSig baseType)
        {
            var type = new TypeDef { Index = Model.Types.Length, Name = name, Namespace = "Fixture", Assembly = Assembly,
                Token = (uint)(0x02000001 + Model.Types.Length), Flags = 1, BaseType = baseType };
            type.Sig = Model.Sigs.TypeDef(type); Model.Types = [..Model.Types, type]; Assembly.Types.Add(type);
            ((Dictionary<string, TypeDef>)Get(Model, "_typesByName")!)[type.ReflectionName] = type;
            return type;
        }

        private MethodDef Method(TypeDef owner, string name, ulong address, bool isStatic, params ParamDef[] parameters)
        {
            for (int i = 0; i < parameters.Length; i++) parameters[i].Position = i;
            var method = new MethodDef { Index = Model.Methods.Length, DeclaringType = owner, Name = name,
                ReturnType = Model.Sigs.Primitive(Il2CppTypeEnum.Void), Address = address,
                Token = (uint)(0x06000001 + Model.Methods.Length),
                Flags = (ushort)(6 | MethodDef.HideBySig | (isStatic ? MethodDef.Static : 0)),
                Slot = MethodDef.InvalidSlot, Parameters = parameters };
            owner.Methods = [..owner.Methods, method]; Model.Methods = [..Model.Methods, method];
            Model.MethodsByAddress[address] = [method];
            return method;
        }

        public (HMethod H, HCall Call, HLocal Owner, HExpr Child, HExpr Index) Build(bool dominates, bool related)
        {
            var fn = new Function { Address = Caller.Address, End = Caller.Address + 0x50, Regs = RegisterModel.Arm64 };
            Block Block(int id)
            {
                var block = new Block { Id = id, Start = Caller.Address + (ulong)(16 * id), End = Caller.Address + (ulong)(16 * id + 8) };
                fn.Blocks.Add(block); return block;
            }
            Block entry = Block(0), fact = Block(1), other = Block(2), use = Block(3), exit = Block(4);
            void Edge(Block from, Block to) { from.Succs.Add(to); to.Preds.Add(from); }
            if (dominates)
            {
                Edge(entry, fact); Edge(entry, exit); Edge(fact, other); Edge(fact, use); Edge(other, use);
            }
            else
            {
                Edge(entry, fact); Edge(entry, other); Edge(fact, use); Edge(other, use);
            }
            Node owner = fn.NewNode(Op.Param, VT.I64, null), child = fn.NewNode(Op.Param, VT.I64, null), index = fn.NewNode(Op.Param, VT.I64, null);
            Node metadata = fn.NewNode(Op.Const, VT.I64, null); metadata.Imm = 0;
            Node call = fn.NewNode(Op.Call, VT.None, use, owner, child, index, metadata); call.Addr = use.Start;
            call.Aux = new CallInfo { Target = AddChild.Address,
                Slots = [new(ArgSlotKind.IntReg, 0), new(ArgSlotKind.IntReg, 1), new(ArgSlotKind.IntReg, 2), new(ArgSlotKind.IntReg, 3)] };
            use.Nodes.Add(call);
            Node condition = fn.NewNode(Op.Const, VT.I1, null); condition.Imm = 1;
            foreach (Block block in fn.Blocks)
            {
                Node terminator = block.Succs.Count switch
                {
                    0 => fn.NewNode(Op.Return, VT.None, block),
                    1 => fn.NewNode(Op.Jump, VT.None, block),
                    _ => fn.NewNode(Op.Branch, VT.None, block, condition)
                };
                terminator.Addr = block.End - 4; block.Nodes.Add(terminator);
            }
            var lifted = new LiftedMethod { Function = fn, Method = Caller,
                Abi = Analysis.Abi.For(Caller, [], []), Normalization = new NormalizeResult() };
            var builder = new HirBuilder(Analysis, lifted);
            var h = (HMethod)Get(builder, "_h")!;
            var hb = new HBlock { Id = use.Id }; h.Blocks.Add(hb);
            HVar local = h.NewLocal(Task.Sig, "guardedParent");
            var receiver = new HLocal(local) { Type = Task.Sig };
            HExpr childValue = new HArg(1) { Type = Task.Sig }, indexValue = new HArg(2) { Type = Int };
            hb.Statements.Add(new HAssign(receiver, new HArg(0) { Type = Task.Sig }));
            var meanings = (IDictionary)Get(builder, "_sem")!;
            object Sem(HExpr expression) => Activator.CreateInstance(SVal, All, null, [expression], null)!;
            meanings[owner] = Sem(receiver); meanings[child] = Sem(childValue); meanings[index] = Sem(indexValue);
            Set(builder, "_cur", hb); Set(builder, "_block", use); Set(builder, "_node", call); Set(builder, "_cfg", new Cfg(fn));
            ((Dictionary<Node, int>)Get(builder, "_position")!)[call] = 0;
            ((Dictionary<Block, HBlock>)Get(builder, "_hblock")!)[use] = hb;
            // These are existing successful type-test facts. The production CFG decides whether the
            // success block dominates this call; the delta does not retest type-test recognition itself.
            ((Dictionary<Block, List<(Node Object, TypeSig Type)>>)Get(builder, "_typeFacts")!)[fact] = [(owner, related ? Parent.Sig : Other.Sig)];
            MethodInfo build = typeof(HirBuilder).GetMethods(All).Single(m => m.Name == "BuildCall" && m.GetParameters().Length == 13);
            try
            {
                build.Invoke(builder, [call, AddChild, Array.Empty<TypeSig>(), Array.Empty<TypeSig>(), false, false,
                    null, false, null, 0, false, false, null]);
            }
            catch (TargetInvocationException e) when (e.InnerException != null)
            {
                System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(e.InnerException).Throw();
                throw;
            }
            HCall result = hb.Statements.OfType<HEval>().Select(e => e.Expression).OfType<HCall>().Single();
            return (h, result, receiver, childValue, indexValue);
        }
    }

    private static void DominatingReceiver()
    {
        var fixture = new Fixture();
        var yes = fixture.Build(dominates: true, related: true);
        Check(yes.H.Problems.Count == 0, "A dominating ParentTask fact is not downgraded to UnkeptReceiver in a static caller");
        Check(ReferenceEquals(yes.Call.This, yes.Owner), "The original declared Task local remains the exact receiver object");
        Check(!yes.Call.ReceiverUnused && yes.Call.UnusedReceiverTarget == null, "An ordinary callee that reads this receives no unused-this/direct attestation");
        Check(yes.Call.Arguments.Length == 2 && ReferenceEquals(yes.Call.Arguments[0], yes.Child) && ReferenceEquals(yes.Call.Arguments[1], yes.Index),
            "Both real managed arguments retain their identity and order");

        var bypass = fixture.Build(dominates: false, related: true);
        Check(bypass.H.Problems.Any(p => p.Contains("object the code did not keep")), "A class test on only one incoming path cannot prove the receiver");
        Check(bypass.Call.This is HConst { Value: null } && !bypass.Call.ReceiverUnused, "A nondominating fact remains a visible unresolved receiver without direct permission");

        var unrelated = fixture.Build(dominates: true, related: false);
        Check(unrelated.H.Problems.Any(p => p.Contains("object the code did not keep")), "A dominating sibling-class fact does not prove ParentTask");
        Check(unrelated.Call.This is HConst { Value: null } && !unrelated.Call.ReceiverUnused, "An unrelated fact does not manufacture a receiver or direct permission");
    }
}
