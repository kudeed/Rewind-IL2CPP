using System.Runtime.CompilerServices;
using Rewind.Analysis;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Recover;
using Rewind.Analysis.X64;
using Rewind.Model;
using Rewind.Runtime;

internal static partial class Program
{
    private static void Set(object owner, string field, object value) => owner.GetType().GetField(field, All)!.SetValue(owner, value);

    private static void Arm64Results()
    {
        foreach ((CallReturn returns, int words, bool pair) in new[] {
            (CallReturn.Unknown, 0, true), (CallReturn.Integer, 2, true), (CallReturn.Integer, 1, false),
            (CallReturn.Void, 0, false), (CallReturn.Float, 0, false), (CallReturn.Double, 0, false) })
        {
            var function = new Function { Regs = RegisterModel.Arm64 };
            var block = new Block(); function.Blocks.Add(block);
            var builder = new IrBuilder(function) { Current = block };
            var variables = (VT[])typeof(A64Lifter).GetField("VarTypes", All)!.GetValue(null)!;
            var ssa = new SsaBuilder(function, variables);
            var lifter = (A64Lifter)RuntimeHelpers.GetUninitializedObject(typeof(A64Lifter));
            Set(lifter, "_b", builder); Set(lifter, "_ssa", ssa); Set(lifter, "_block", block);
            Node old = builder.Const(VT.I64, 9723); ssa.Write(1, block, old);
            Node call = builder.Raw(Op.Call, VT.None);
            CallShape? shape = returns == CallReturn.Unknown ? null : new CallShape { Returns = returns, IntResults = words };
            typeof(A64Lifter).GetMethod("AfterCall", All)!.Invoke(lifter, [call, shape, returns]);
            Node x1 = ssa.Read(1, block);
            Check(pair ? x1.Op == Op.Proj && x1.Imm == CallResult.IntReturn2 && ReferenceEquals(x1.In[0], call) : x1.Op == Op.Undef,
                "x1 is a captured result only for an unknown or proved two-word return");
            Check(!ReferenceEquals(old, x1), "a call never preserves the old caller-clobbered x1");
        }
        Cases.Add("ARM64 unknown indirect pair and known scalar/void/float ABI");
    }

    private sealed record StorageFixture(HirBuilder Builder, TypeSig Type, TypeSig Previous, Dictionary<int, Node> Projections,
        Function Function, Node LowStore, Node HighStore, Node LowRead, Node HighRead, Node OldFill, Node OldRead, Node ReturnCall,
        Dictionary<int, TypeSig> Types, Dictionary<int, HashSet<TypeSig>> Copies, LayoutCalculator Layouts);

    private static StorageFixture Storage(bool previous = true)
    {
        var pair = Define("TaskPair", true, ("source", Object), ("token", Sigs.Primitive(Il2CppTypeEnum.I2)));
        var old = Define("GenericTask", true, ("source", Object), ("result", Object), ("more", Object), ("token", Int));
        var container = Define("Layouts", true, ("new", pair.Sig), ("old", old.Sig));
        LayoutCalculator layouts = Layouts(container.Sig);
        var model = (Il2CppModel)RuntimeHelpers.GetUninitializedObject(typeof(Il2CppModel)); Backing(model, "Sigs", Sigs);
        var program = (ProgramAnalysis)RuntimeHelpers.GetUninitializedObject(typeof(ProgramAnalysis));
        Backing(program, "Model", model); Backing(program, "Layouts", layouts);
        var function = new Function { Regs = RegisterModel.Arm64 }; var block = new Block(); function.Blocks.Add(block);
        var ir = new IrBuilder(function) { Current = block };
        Node sp = function.NewNode(Op.Param, VT.I64, null); function.Params[RegisterModel.Arm64.StackPointer] = sp;
        Node Address(int offset) => ir.Add(sp, ir.Const(VT.I64, offset));
        Node at = Address(-64), highAt = Address(-56);
        var info = new CallInfo { Slots = [new ArgSlot(ArgSlotKind.IntReg, 8)] };
        ir.CurrentAddr = 0x1000; Node fill = ir.Raw(Op.Call, VT.None, at); fill.Aux = info;
        ir.CurrentAddr = 0x1004; Node read = ir.Raw(Op.Call, VT.None, at); read.Aux = info;
        ir.CurrentAddr = 0x1010; Node call = ir.Raw(Op.Call, VT.None); call.Aux = new CallInfo();
        Node low = ir.Raw(Op.Proj, VT.I64, call); low.Imm = CallResult.IntReturn;
        Node high = ir.Raw(Op.Proj, VT.I64, call); high.Imm = CallResult.IntReturn2;
        ir.CurrentAddr = 0x1014; Node store0 = ir.Raw(Op.Store, VT.None, at, low); Node store1 = ir.Raw(Op.Store, VT.None, highAt, high);
        ir.CurrentAddr = 0x1018; Node load0 = ir.Raw(Op.Load, VT.I64, at); Node load1 = ir.Raw(Op.Load, VT.I64, highAt);
        ir.Raw(Op.Return, VT.None, load0, load1);
        var types = new Dictionary<int, TypeSig>(); if (previous) types[-64] = old.Sig;
        var copies = new Dictionary<int, HashSet<TypeSig>>();
        var builder = (HirBuilder)RuntimeHelpers.GetUninitializedObject(typeof(HirBuilder));
        Set(builder, "_p", program); Set(builder, "_m", model); Set(builder, "_fn", function);
        Set(builder, "_method", new MethodDef { DeclaringType = pair });
        Set(builder, "_frameTypes", types); Set(builder, "_copyVotes", copies);
        Set(builder, "_uses", new Dictionary<Node, List<Node>> { [low] = [store0], [high] = [store1] });
        Backing(builder, "FrameConflicts", new HashSet<int>());
        Backing(builder, "ScalarSlotConflicts", new HashSet<int>());
        return new StorageFixture(builder, pair.Sig, old.Sig,
            new Dictionary<int, Node> { [CallResult.IntReturn] = low, [CallResult.IntReturn2] = high },
            function, store0, store1, load0, load1, fill, read, call, types, copies, layouts);
    }
    private static void Recognize(StorageFixture f) => typeof(HirBuilder).GetMethod("RegisterResultStorage", All)!.Invoke(f.Builder, [f.Projections, f.Type]);

    private static void StackResultLifetimes()
    {
        var f = Storage(); Recognize(f);
        Check(f.Builder.FrameConflicts.SetEquals([-64]), "complete returned pair exposes a different struct lifetime despite compatible prefix fields");
        Check(f.Builder.ScalarSlotConflicts.SetEquals([-64]), "proved conflicting return storage opts into strict untaken-argument filtering");
        int Extent(Node call, int input) => ReferenceEquals(call, f.OldFill) || ReferenceEquals(call, f.OldRead) ? 32 : StackPromotion.NotTaken;
        int moved = StackSplitting.Run(f.Function, f.Builder.FrameConflicts, Extent,
            (call, _) => ReferenceEquals(call, f.OldFill), (call, _) => ReferenceEquals(call, f.OldRead));
        Check(moved > 0, "existing reaching-definition pass separates proven stack lifetimes");
        Check(Offset(f.LowStore.In[0]) == Offset(f.LowRead.In[0]) && Offset(f.HighStore.In[0]) == Offset(f.HighRead.In[0]),
            "each later field still reads the exact store of its own lifetime");
        Check(!Overlaps(Offset(f.LowRead.In[0]), 8, Offset(f.OldRead.In[0]), 32) &&
            !Overlaps(Offset(f.HighRead.In[0]), 8, Offset(f.OldRead.In[0]), 32), "new and old values no longer share a typed stack region");
        Check(ReferenceEquals(f.HighStore.In[1], f.Projections[CallResult.IntReturn2]), "operation/token tail remains the captured second return word");
        Cases.Add("returned pair and reused larger generic stack lifetime");
        UntakenStackReads();

        var newStorage = Storage(false); Recognize(newStorage);
        Check(newStorage.Copies.TryGetValue(-64, out var votes) && votes.Single().Key == newStorage.Type.Key,
            "complete pair types an otherwise untyped stack copy");
        var same = Storage(); same.Types[-64] = same.Type; Recognize(same);
        Check(same.Builder.FrameConflicts.Count == 0, "same exact struct is not a type conflict");
        var nested = Storage();
        var wrapper = Define("Wrapper", true, ("task", nested.Type));
        var cache = (Dictionary<TypeSig, TypeLayout>)typeof(LayoutCalculator).GetField("_cache", All)!.GetValue(nested.Layouts)!;
        cache[wrapper.Sig] = new TypeLayout { Size = 16, Fields = [new FieldSlot(wrapper.Fields[0], nested.Type, 0, 16)] };
        nested.Types[-64] = wrapper.Sig; Recognize(nested);
        Check(nested.Builder.FrameConflicts.Count == 0, "an exact nested field at offset zero is a valid view");
        void Reject(string name, Action<StorageFixture> change)
        {
            var candidate = Storage(); change(candidate); Recognize(candidate);
            Check(candidate.Builder.FrameConflicts.Count == 0 && candidate.Copies.Count == 0, name); Cases.Add(name);
        }
        Reject("one word is not a complete returned struct", x => x.Projections.Remove(CallResult.IntReturn2));
        Reject("different store instructions are not a proved STP copy", x => x.HighStore.Addr += 4);
        Reject("unknown return layout is not a lifetime proof", x => x.Layouts.Of(x.Type).Known = false);
        Reject("overlapping return fields are not a lifetime proof", x => {
            var layout = x.Layouts.Of(x.Type); layout.Fields[1] = layout.Fields[1] with { Offset = 0 };
        });
        Reject("incorrect substituted field types are refused", x => {
            var layout = x.Layouts.Of(x.Type); layout.Fields[1] = layout.Fields[1] with { Type = Int };
        });
        Reject("a modified second word is not the original pair", x => x.HighStore.In[1] = new Node { Op = Op.Const, Type = VT.I64, Imm = 0 });
        Reject("a truncated payload is not restored from its type", x => {
            Node high = x.Projections[CallResult.IntReturn2];
            Node narrow = new() { Op = Op.And, Type = VT.I64, In = [high, new Node { Op = Op.Const, Type = VT.I64, Imm = 255 }] };
            x.HighStore.In[1] = narrow;
            Set(x.Builder, "_uses", new Dictionary<Node, List<Node>> {
                [x.Projections[CallResult.IntReturn]] = [x.LowStore], [high] = [narrow], [narrow] = [x.HighStore] });
        });
        static int Offset(Node address) => address.Op == Op.Add ? checked((int)IrBuilder.SImm(address.In[1])) : 0;
        static bool Overlaps(int a, int width, int b, int size) => a < b + size && b < a + width;
    }

    private static void UntakenStackReads()
    {
        foreach (bool trulyTaken in new[] { false, true })
        {
            var f = Storage();
            Block entry = f.Function.Entry, written = new() { Id = 1 }, join = new() { Id = 2 };
            f.Function.Blocks.AddRange([written, join]);
            int first = entry.Nodes.IndexOf(f.ReturnCall);
            foreach (Node node in entry.Nodes.Skip(first).ToArray())
            {
                entry.Nodes.Remove(node); node.Block = written; written.Nodes.Add(node);
            }
            var ir = new IrBuilder(f.Function) { Current = entry };
            ir.Raw(Op.Branch, VT.None, ir.Const(VT.I32, 1));
            entry.Succs.AddRange([written, join]); written.Preds.Add(entry); join.Preds.AddRange([entry, written]); written.Succs.Add(join);
            written.Nodes.RemoveAt(written.Nodes.Count - 1); // replace the old return with a real by-value consumer
            ir.Current = written;
            Node consumer = ir.Raw(Op.Call, VT.None, f.LowRead, f.HighRead); consumer.Aux = new CallInfo();
            ir.Raw(Op.Jump, VT.None);
            ir.Current = join;
            Node sp = f.Function.Params[f.Function.Regs.StackPointer];
            var captures = new List<Node>();
            for (int i = 0; i < 4; i++)
                captures.Add(ir.Raw(Op.Load, VT.I64, ir.Add(sp, ir.Const(VT.I64, -64 + i * 8))));
            Node later = ir.Raw(Op.Call, VT.None, [.. captures]); later.Aux = new CallInfo();
            ir.Raw(Op.Return, VT.None);
            Recognize(f);
            int Extent(Node call, int input) => ReferenceEquals(call, f.OldFill) || ReferenceEquals(call, f.OldRead) ? 32 :
                ReferenceEquals(call, later) ? trulyTaken ? 0 : StackPromotion.NotTaken : 0;
            int Split(ISet<int>? hints) => StackSplitting.Run(f.Function, f.Builder.FrameConflicts, Extent,
                (call, _) => ReferenceEquals(call, f.OldFill), (call, _) => ReferenceEquals(call, f.OldRead), lenient: hints);
            Check(Split(null) == 0, "captured join arguments conservatively tie both branch lifetimes without an exact conflict proof");
            int moved = Split(f.Builder.ScalarSlotConflicts);
            Check(trulyTaken ? moved == 0 : moved > 0, trulyTaken
                ? "real argument reads keep observing both paths and are never ignored"
                : "proved unused ABI captures no longer tie distinct returned-value lifetimes");
            if (!trulyTaken)
            {
                int At(Node address) => checked((int)IrBuilder.SImm(address.In[1]));
                Check(At(f.LowStore.In[0]) == At(f.LowRead.In[0]) && At(f.HighStore.In[0]) == At(f.HighRead.In[0]) &&
                    At(f.OldRead.In[0]) != At(f.LowRead.In[0]), "real reads retain their matching stores after speculative captures are excluded");
                Check(ReferenceEquals(consumer.In[0], f.LowRead) && ReferenceEquals(consumer.In[1], f.HighRead),
                    "the actual by-value call still takes both original returned words");
            }
        }
        Cases.Add("real CFG join with unused versus consumed captured stack arguments");
    }
}
