using System.Collections;
using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis;
using Rewind.Analysis.Abi;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Runtime;
using HostRuntime = System.Runtime.CompilerServices.RuntimeHelpers;
using Helpers = Rewind.Analysis.Runtime.RuntimeHelpers;

internal static class Program
{
    private const BindingFlags All = BindingFlags.Instance | BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic;
    private static int assertions;
    private static string? journal;
    private static readonly string RunId = Guid.NewGuid().ToString("N");
    private static readonly Type SVal = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.SVal")!;
    private static readonly Type SVTable = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.SVTable")!;

    private static int Main(string[] args)
    {
        string? report = null;
        var selected = new HashSet<string>(StringComparer.Ordinal);
        for (int i = 0; i < args.Length; i++)
        {
            if (i + 1 == args.Length) throw new ArgumentException("Missing option value");
            string option = args[i], value = args[++i];
            if (option == "--group") selected.UnionWith(value.Split(',', StringSplitOptions.RemoveEmptyEntries));
            else if (option == "--report") report = value;
            else if (option == "--journal") journal = value;
            else throw new ArgumentException("Usage: --group declared,dominance,pointers,casts,precision --report file --journal jsonl");
        }
        if (Environment.GetEnvironmentVariable("REWIND_NO_CAST_DOMINANCE") != null ||
            Environment.GetEnvironmentVariable("REWIND_NO_PARAMETER_SLOTS") != null)
            throw new InvalidOperationException("Run with production dominance/parameter-slot options enabled.");
        journal ??= report == null ? null : report + ".groups.jsonl";
        var groups = new (string Id, Action Run)[]
        {
            ("declared", DeclaredContracts), ("dominance", DominatingFacts),
            ("pointers", EarlierPointers), ("casts", CastPlaces), ("precision", PrecisionBoundaries)
        };
        if (selected.Except(groups.Select(g => g.Id)).Any()) throw new ArgumentException("Unknown group");
        var results = new List<object>();
        bool failed = false;
        foreach (var group in groups)
        {
            if (selected.Count != 0 && !selected.Contains(group.Id)) continue;
            int before = assertions;
            string? error = null;
            try { group.Run(); }
            catch (Exception ex) { error = ex.ToString(); failed = true; }
            var item = new { run_id = RunId, group = group.Id, status = error == null ? "pass" : "fail", assertions = assertions - before, error };
            results.Add(item);
            string line = JsonSerializer.Serialize(item);
            Console.WriteLine(line);
            if (journal != null) File.AppendAllText(journal, line + Environment.NewLine);
        }
        var summary = new
        {
            suite = "virtual-dispatch-proofs", run_id = RunId, assertions, groups = results,
            analysis_binary_sha256 = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(typeof(HirBuilder).Assembly.Location))),
            scope = "New virtual dispatch proof fixtures only; no historical tests, native recovery or Unity."
        };
        string json = JsonSerializer.Serialize(summary, new JsonSerializerOptions { WriteIndented = true });
        Console.WriteLine(json);
        if (report != null) File.WriteAllText(report, json + Environment.NewLine);
        return failed ? 1 : 0;
    }

    private static void Check(bool value, string why)
    {
        assertions++;
        if (!value) throw new InvalidOperationException(why);
    }
    private static void Same(object? actual, object? expected, string why) => Check(ReferenceEquals(actual, expected), why);
    private static void Set(object target, string name, object value) => target.GetType().GetField(name, All)!.SetValue(target, value);
    private static void Backing(object target, string name, object value) => Set(target, "<" + name + ">k__BackingField", value);
    private static object? Invoke(object target, string name, params object?[] values)
    {
        var method = target.GetType().GetMethods(All).Single(m => m.Name == name && m.GetParameters().Length == values.Length);
        try { return method.Invoke(target, values); }
        catch (TargetInvocationException ex) when (ex.InnerException != null)
        {
            System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(ex.InnerException).Throw();
            throw;
        }
    }
    private static object NewSem(Type type, params object[] values) => Activator.CreateInstance(type, All, null, values, null)!;
    private sealed class Image : NativeImage
    {
        public override ImageFormat Format => ImageFormat.Elf;
        public Image() { Arch = CpuArch.Arm64; PointerSize = 8; MemoryBase = 0; Memory = new byte[16]; }
    }

    // The actual HirBuilder constructor initializes all its caches/collections. The small metadata model
    // supplies every dependency used here; no ELF parsing, lifter or partially initialized builder is used.
    private sealed class Fixture
    {
        public readonly SigFactory Sigs = new();
        public readonly Il2CppModel Model;
        public readonly Function Function = new() { Regs = RegisterModel.Arm64 };
        public readonly Block Entry = new() { Id = 0 }, Yes = new() { Id = 1 }, No = new() { Id = 2 }, Join = new() { Id = 3 }, After = new() { Id = 4 }, Dead = new() { Id = 5 };
        public readonly TypeDef Root, Child, Other, Interface;
        public readonly MethodDef RootMethod, ChildMethod, InterfaceMethod;
        public readonly Node Object;
        public readonly HirBuilder Builder;
        public readonly IDictionary Meanings;
        private readonly Dictionary<Block, List<(Node Object, TypeSig Type)>> facts;
        private int nextType, nextMethod;

        public Fixture()
        {
            var image = new Image();
            var binary = (Il2CppBinary)typeof(Il2CppBinary).GetConstructor(All, null, [typeof(NativeImage), typeof(int)], null)!.Invoke([image, 3900]);
            Model = (Il2CppModel)HostRuntime.GetUninitializedObject(typeof(Il2CppModel));
            Backing(Model, "Image", image); Backing(Model, "Binary", binary); Backing(Model, "Sigs", Sigs);
            Backing(Model, "MethodsByAddress", new Dictionary<ulong, List<MethodDef>>());
            Backing(Model, "InstsByAddress", new Dictionary<ulong, List<MethodInst>>());
            Set(Model, "_typesByName", new Dictionary<string, TypeDef>(StringComparer.Ordinal));
            Model.Types = []; Model.Methods = []; Model.MethodInsts = [];
            Model.Assemblies = []; Model.Fields = []; Model.Parameters = []; Model.GenericParams = [];
            Root = Type("Root"); Child = Type("Child", Root); Other = Type("Other", Root);
            Interface = Type("IFace"); Interface.Flags = TypeDef.Interface | TypeDef.Abstract;
            RootMethod = Method(Root, "BaseSlot", 0);
            ChildMethod = Method(Child, "DerivedSlot", 1);
            InterfaceMethod = Method(Interface, "InterfaceRelativeZero", 0);
            var interfaceImpl = Method(Child, "InterfaceImplementation", 2);
            interfaceImpl.Flags |= MethodDef.Final;
            Root.VTable = [Encode(RootMethod)]; Child.VTable = [Encode(RootMethod), Encode(ChildMethod), Encode(interfaceImpl)];
            Other.VTable = [Encode(RootMethod)];
            Child.Interfaces = [Interface.Sig]; Child.InterfaceOffsets = [(Interface.Sig, 2)];

            Function.Blocks.AddRange([Entry, Yes, No, Join, After, Dead]);
            Edge(Entry, Yes); Edge(Entry, No); Edge(Yes, Join); Edge(No, Join); Edge(Join, After);
            Object = Function.NewNode(Op.Param, VT.I64, null);
            var owner = Type("Caller");
            var method = new MethodDef { Name = "Probe", DeclaringType = owner, ReturnType = Sigs.Primitive(Il2CppTypeEnum.Void), Flags = MethodDef.Static, Slot = MethodDef.InvalidSlot };
            var layouts = new LayoutCalculator(Model);
            var abi = new Aapcs64Abi(Model, layouts);
            var program = (ProgramAnalysis)HostRuntime.GetUninitializedObject(typeof(ProgramAnalysis));
            Backing(program, "Model", Model); Backing(program, "Layouts", layouts); Backing(program, "Abi", abi);
            Backing(program, "Helpers", new Helpers()); Backing(program, "Context", new ModelCodeContext(Model));
            var lifted = new LiftedMethod { Method = method, Function = Function, Abi = abi.For(method, [], []), Normalization = new NormalizeResult() };
            Builder = new HirBuilder(program, lifted);
            Set(Builder, "_cfg", new Cfg(Function));
            Meanings = (IDictionary)typeof(HirBuilder).GetField("_sem", All)!.GetValue(Builder)!;
            Meanings[Object] = NewSem(SVal, new HArg(0) { Type = Root.Sig });
            facts = (Dictionary<Block, List<(Node Object, TypeSig Type)>>)typeof(HirBuilder).GetField("_typeFacts", All)!.GetValue(Builder)!;
            At(Entry);
        }

        public TypeDef Type(string name, TypeDef? parent = null)
        {
            var t = new TypeDef { Index = nextType++, Name = name, BaseType = parent?.Sig, Assembly = new AssemblyModel { Name = "Fixture" } };
            t.Sig = Sigs.TypeDef(t); Model.Types = [..Model.Types, t]; return t;
        }
        public MethodDef Method(TypeDef owner, string name, ushort slot)
        {
            var m = new MethodDef { Index = nextMethod++, Name = name, Slot = slot, DeclaringType = owner, Flags = MethodDef.Virtual | MethodDef.NewSlot, ReturnType = Sigs.Primitive(Il2CppTypeEnum.Void) };
            owner.Methods = [..owner.Methods, m]; Model.Methods = [..Model.Methods, m]; return m;
        }
        public static uint Encode(MethodDef m) => ((uint)UsageKind.MethodDef << 29) | ((uint)m.Index << 1);
        public static void Edge(Block from, Block to) { from.Succs.Add(to); to.Preds.Add(from); }
        public void Fact(Block at, TypeSig type, Node? obj = null)
        {
            if (!facts.TryGetValue(at, out var values)) facts[at] = values = [];
            values.Add((obj ?? Object, type));
        }
        public void ClearFacts() => facts.Clear();
        public Node Node(Block block, Op op = Op.Load)
        {
            var n = Function.NewNode(op, VT.I64, block); block.Nodes.Add(n);
            ((Dictionary<Node, int>)typeof(HirBuilder).GetField("_position", All)!.GetValue(Builder)!)[n] = block.Nodes.Count - 1;
            return n;
        }
        public void At(Block block, Node? node = null)
        {
            Set(Builder, "_block", block); Set(Builder, "_node", node ?? Node(block, Op.Call));
        }
        public TypeSig? Receiver(TypeSig? inferred = null, Node? at = null, Node? obj = null) =>
            (TypeSig?)Invoke(Builder, "VirtualReceiverType", obj ?? Object, inferred ?? Root.Sig, at);
        public MethodDef? Resolve(TypeSig? receiver, int slot) => (MethodDef?)Invoke(Builder, "FindVirtual", receiver, slot);
        public Node Pointer(Block block, int slot = 1, Node? obj = null)
        {
            Node n = Node(block); Meanings[n] = NewSem(SVTable, obj ?? Object, slot, false); return n;
        }
        public Node Merge(params Node[] inputs) => new() { Op = Op.Phi, Type = VT.I64, Block = Join, In = inputs };
        public MethodDef[]? Merged(Node phi) => (MethodDef[]?)Invoke(Builder, "MergedVirtualTargets", phi);
        public MethodDef? OneMerged(Node phi, Node? receiver = null) => (MethodDef?)Invoke(Builder, "OneMergedVirtualTarget", phi, receiver ?? Object);
        public HExpr? PointerExpr(Node pointer) => (HExpr?)Invoke(Builder, "VirtualPointer", Meanings[pointer], pointer);
        public void Cast(Block at, Node check, TypeSig? type = null)
        {
            var casts = (Dictionary<Node, List<TypeSig>>)typeof(HirBuilder).GetField("_castTypes", All)!.GetValue(Builder)!;
            casts[Object] = [type ?? Child.Sig];
            Invoke(Builder, "AddCastPlace", Object, at, check, null);
        }
    }

    private static void DeclaredContracts()
    {
        var f = new Fixture();
        Same(f.Resolve(f.Root.Sig, 0), f.RootMethod, "Known class contract is resolved");
        Same(f.Resolve(f.Child.Sig, 0), f.RootMethod, "Inherited contract stays at its introducing ancestor");
        Same(f.Resolve(f.Child.Sig, 1), f.ChildMethod, "Declared derived contract is resolved");
        Same(f.Resolve(f.Root.Sig, 1), null, "One known descendant with a slot does not prove an unguarded Root is Child");
        Same(f.Resolve(f.Root.Sig, 15), null, "Unknown slot stays unresolved");
        var generic = f.Type("GenericChild", f.Root);
        generic.GenericParameters = [new GenericParam { Index = 0, Name = "T", OwnerType = generic }];
        var g1 = f.Method(generic, "GenericSlotOne", 1); var g2 = f.Method(generic, "GenericSlotTwo", 2);
        var gm = f.Method(generic, "GenericOnly", 3); gm.ReturnType = f.Sigs.GenericParam(generic.GenericParameters[0]);
        generic.VTable = [Fixture.Encode(f.RootMethod), Fixture.Encode(g1), Fixture.Encode(g2), Fixture.Encode(gm)];
        Same(f.Resolve(f.Root.Sig, 3), null, "Open generic descendant cannot manufacture missing class arguments");
        var otherMethod = f.Method(f.Other, "UnrelatedSlot", 1);
        f.Other.VTable = [Fixture.Encode(f.RootMethod), Fixture.Encode(otherMethod)];
        Same(f.Resolve(f.Root.Sig, 1), null, "Unrelated descendant contracts remain unresolved");
        Same(f.Resolve(null, 1), null, "Missing receiver type remains unresolved");
    }

    private static void DominatingFacts()
    {
        var f = new Fixture(); f.Fact(f.Yes, f.Child.Sig); f.At(f.Yes);
        Same(f.Receiver(), f.Child.Sig, "Successful type-test dominates its own successor");
        Same(f.Resolve(f.Receiver(), 1), f.ChildMethod, "Guarded child virtual contract is retained");
        f.At(f.No); Same(f.Receiver(), f.Root.Sig, "Other branch cannot borrow a type-test fact");
        f.At(f.Join); Same(f.Receiver(), f.Root.Sig, "A join reached through an unchecked path cannot borrow the fact");
        f.Fact(f.Dead, f.Child.Sig); f.At(f.Dead); Same(f.Receiver(), f.Root.Sig, "Unreachable block supplies no type fact");
        f.At(f.Yes); var otherObject = f.Function.NewNode(Op.Param, VT.I64, null);
        Same(f.Receiver(obj: otherObject), f.Root.Sig, "Facts belong to the exact SSA object");
        var i = new Fixture(); i.Fact(i.Yes, i.Interface.Sig); i.At(i.Yes);
        Same(i.Receiver(i.Child.Sig), i.Child.Sig, "An interface test cannot replace the known class type");
        Same(i.Resolve(i.Receiver(i.Child.Sig), 0), i.RootMethod, "Interface-relative slot zero is not class-vtable slot zero");
        var weaker = new Fixture(); weaker.Fact(weaker.Yes, weaker.Root.Sig); weaker.At(weaker.Yes);
        Same(weaker.Receiver(weaker.Child.Sig), weaker.Child.Sig, "A weaker class test cannot discard a more precise receiver type");
    }

    private static void EarlierPointers()
    {
        var f = new Fixture(); var a = f.Pointer(f.Yes); var b = f.Pointer(f.No); var phi = f.Merge(a, b);
        // Model a successful check after the pointer values joined, before their eventual call.
        // It is valid at this call but cannot be moved into either earlier pointer read.
        f.Fact(f.After, f.Child.Sig); f.At(f.After);
        Same(f.Receiver(), f.Child.Sig, "Current guarded call can use its own class fact");
        Same(f.Receiver(at: a), f.Root.Sig, "Later fact does not dominate the first earlier pointer read");
        Same(f.Merged(phi), null, "MergedVirtualTargets does not project a later call fact onto incoming reads");
        Same(f.OneMerged(phi), null, "OneMergedVirtualTarget does not project a later call fact onto incoming reads");
        Same(f.PointerExpr(a), null, "VirtualPointer preserves an unresolved earlier read");

        var p = new Fixture(); p.Fact(p.Yes, p.Child.Sig);
        var left = new Block { Id = 6 }; var right = new Block { Id = 7 }; var merge = new Block { Id = 8 };
        p.Yes.Succs.Remove(p.Join); p.Join.Preds.Remove(p.Yes);
        p.Function.Blocks.AddRange([left, right, merge]);
        Fixture.Edge(p.Yes, left); Fixture.Edge(p.Yes, right); Fixture.Edge(left, merge); Fixture.Edge(right, merge); Fixture.Edge(merge, p.Join);
        Set(p.Builder, "_cfg", new Cfg(p.Function));
        var x = p.Pointer(left); var y = p.Pointer(right); p.At(merge);
        var innerPhi = new Node { Op = Op.Phi, Type = VT.I64, Block = merge, In = [x, y] };
        Same(p.Receiver(at: x), p.Child.Sig, "A fact dominating an earlier read remains usable");
        var picked = p.Merged(innerPhi);
        Check(picked is { Length: 2 } && ReferenceEquals(picked[0], p.ChildMethod) && ReferenceEquals(picked[1], p.ChildMethod), "Each merged input uses its own proven read context");
        Same(p.OneMerged(innerPhi), p.ChildMethod, "Common proven earlier pointer target is retained");
        Check(p.PointerExpr(x) is HMethodPointer ptr && ReferenceEquals(ptr.Method, p.ChildMethod), "Proven earlier pointer emits its exact contract");
        var different = p.Function.NewNode(Op.Param, VT.I64, null);
        Same(p.OneMerged(innerPhi, different), null, "One merged pointer must still match the call receiver identity");
        var unknown = new Node { Op = Op.Load, Type = VT.I64 };
        Same(p.Receiver(at: unknown), p.Root.Sig, "A pointer with no location cannot borrow current facts");
    }

    private static void CastPlaces()
    {
        var f = new Fixture(); Node check = f.Node(f.Yes, Op.Load); f.Cast(f.Yes, check);
        f.At(f.No); Same(f.Receiver(), f.Root.Sig, "A unique cast elsewhere is not a proof on this branch");
        f.At(f.Join); Same(f.Receiver(), f.Root.Sig, "A cast on one incoming arm is not a proof at the join");
        Node after = f.Node(f.Yes, Op.Call); f.At(f.Yes, after);
        Same(f.Receiver(), f.Child.Sig, "A dominating checked cast remains usable by the current call");
        Node earlier = f.Pointer(f.Entry);
        Same(f.Receiver(at: earlier), f.Root.Sig, "Current checked cast cannot be projected onto an earlier pointer read");
        var before = new Fixture(); Node firstCall = before.Node(before.Yes, Op.Call); Node laterCheck = before.Node(before.Yes, Op.Load);
        before.Cast(before.Yes, laterCheck); before.At(before.Yes, firstCall);
        Same(before.Receiver(), before.Root.Sig, "A later cast must not move before a side-effecting call");
        var iface = new Fixture(); Node interfaceCheck = iface.Node(iface.Yes, Op.Load); iface.Cast(iface.Yes, interfaceCheck, iface.Interface.Sig); iface.At(iface.Yes);
        Same(iface.Receiver(iface.Child.Sig), iface.Child.Sig, "A checked interface cast also does not select a class slot");
    }
    private static void PrecisionBoundaries()
    {
        var f = new Fixture();
        var genericBase = f.Type("GenericBase", f.Root);
        var baseParameter = new GenericParam { Index = 10, Name = "T", Position = 0, OwnerType = genericBase };
        genericBase.GenericParameters = [baseParameter];
        var genericDerived = f.Type("GenericDerived");
        var derivedParameter = new GenericParam { Index = 11, Name = "T", Position = 0, OwnerType = genericDerived };
        genericDerived.GenericParameters = [derivedParameter];
        genericDerived.BaseType = f.Sigs.GenericInst(genericBase, [f.Sigs.GenericParam(derivedParameter)]);
        var baseInt = f.Sigs.GenericInst(genericBase, [f.Sigs.Primitive(Il2CppTypeEnum.I4)]);
        var baseString = f.Sigs.GenericInst(genericBase, [f.Sigs.Primitive(Il2CppTypeEnum.String)]);
        var derivedInt = f.Sigs.GenericInst(genericDerived, [f.Sigs.Primitive(Il2CppTypeEnum.I4)]);
        var derivedString = f.Sigs.GenericInst(genericDerived, [f.Sigs.Primitive(Il2CppTypeEnum.String)]);
        f.Fact(f.Yes, baseInt); f.At(f.Yes);
        Same(f.Receiver(derivedInt), derivedInt, "Substituted Base<int> proof preserves the more specific Derived<int>");
        Same(f.Receiver(baseString), baseInt, "Matching generic definitions with different arguments are not equal types");
        Same(f.Receiver(derivedString), baseInt, "Derived<string> does not prove an inferred Base<int> ancestor");
        Same(f.Receiver(f.Interface.Sig), baseInt, "An inferred interface never overrides a proven class contract");
        f.ClearFacts(); f.Fact(f.Yes, baseString);
        Same(f.Receiver(derivedInt), baseString, "Known Base<string> cannot retain a merely definition-compatible Derived<int>");

        var unknown = new Fixture(); Node check = unknown.Node(unknown.Yes, Op.Load); unknown.Cast(unknown.Yes, check);
        var noLocation = new Node { Op = Op.Load, Type = VT.I64, In = [unknown.Object] };
        unknown.At(unknown.Yes, noLocation);
        Same(unknown.Receiver(at: noLocation), unknown.Root.Sig, "Even readAt == current node cannot borrow a cast when its location is unknown");
        unknown.At(unknown.Yes); Set(unknown.Builder, "_cfg", null!);
        Same(unknown.Receiver(), unknown.Root.Sig, "No CFG means no new cast proof, despite the older general cast policy");

        var wrongBlock = new Fixture(); Node noCheck = wrongBlock.Node(wrongBlock.No, Op.Load); wrongBlock.Cast(wrongBlock.No, noCheck);
        Node elsewhere = wrongBlock.Pointer(wrongBlock.Yes); wrongBlock.At(wrongBlock.No, elsewhere);
        Same(wrongBlock.Receiver(at: elsewhere), wrongBlock.Root.Sig, "Node identity alone cannot borrow a cast from a different current block");
        var noNode = new Fixture(); Node yesCheck = noNode.Node(noNode.Yes, Op.Load); noNode.Cast(noNode.Yes, yesCheck); noNode.At(noNode.Yes);
        Set(noNode.Builder, "_node", null!);
        Same(noNode.Receiver(), noNode.Root.Sig, "A current cast without a valid node position cannot manufacture proof");
        var unreachable = new Fixture(); Node deadRead = unreachable.Pointer(unreachable.Dead); unreachable.Fact(unreachable.Dead, unreachable.Child.Sig); unreachable.At(unreachable.Dead, deadRead);
        Same(unreachable.Receiver(at: deadRead), unreachable.Root.Sig, "An unreachable read cannot use a locally recorded class fact");
    }

}
