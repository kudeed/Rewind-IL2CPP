using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Recover;
using Rewind.Model;

internal static partial class Program
{
    private static readonly Type ReceiverRule = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.ReceiverRecovery", true)!;
    private sealed record ReceiverFixture(Function Function, Block Guard, Block Throw, Block Next, Node Owner, Node Stale, Node Call);

    private static Function ReceiverCallee(bool reads = false, RegisterModel? registers = null)
    {
        var function = new Function { Regs = registers ?? RegisterModel.Arm64 };
        var block = new Block(); function.Blocks.Add(block);
        var ir = new IrBuilder(function) { Current = block };
        Node result = ir.Const(VT.I64, 7);
        if (reads)
        {
            int register = function.Regs.IntArgs[0];
            var receiver = function.NewNode(Op.Param, VT.I64, null);
            function.Params[register] = receiver;
            result = ir.Raw(Op.Load, VT.I64, ir.Add(receiver, ir.Const(VT.I64, 16)));
        }
        ir.Raw(Op.Return, VT.None, result);
        return function;
    }

    private static bool Ignores(Function function) =>
        (bool)ReceiverRule.GetMethod("DoesNotReadReceiver", All)!.Invoke(null, [function, function.Regs.IntArgs[0]])!;

    private static ReceiverFixture ReceiverSite(bool priorResult = false, bool reversed = false)
    {
        var function = new Function { Regs = RegisterModel.Arm64 };
        Block guard = new() { Id = 0 }, refusal = new() { Id = 1 }, next = new() { Id = 2 };
        function.Blocks.AddRange([guard, refusal, next]);
        guard.Succs.AddRange(reversed ? [next, refusal] : [refusal, next]);
        refusal.Preds.Add(guard); next.Preds.Add(guard);
        var ir = new IrBuilder(function) { Current = guard, CurrentAddr = 0x1000 };
        Node closure = function.NewNode(Op.Param, VT.I64, null); function.Params[0] = closure;
        Node stale = closure;
        if (priorResult)
        {
            var previous = ir.Raw(Op.Call, VT.None); previous.Aux = new CallInfo { Target = 0x3000 };
            stale = ir.Raw(Op.Proj, VT.I64, previous);
        }
        Node owner = ir.Raw(Op.Load, VT.I64, ir.Add(closure, ir.Const(VT.I64, 24)));
        Node condition = ir.Raw(reversed ? Op.CmpNe : Op.CmpEq, VT.I1, owner, ir.Const(VT.I64, 0));
        ir.Raw(Op.Branch, VT.None, condition);
        ir.Current = refusal;
        var raise = ir.Raw(Op.Call, VT.None); raise.Aux = new CallInfo { Target = 0x4000, NoReturn = true };
        ir.Raw(Op.Unreachable, VT.None);
        ir.Current = next; ir.CurrentAddr = 0x1010;
        Node call = ir.Raw(Op.Call, VT.None, stale, ir.Const(VT.I64, 0));
        call.Aux = new CallInfo { Target = 0x2000, Slots = [new ArgSlot(ArgSlotKind.IntReg, 0), new ArgSlot(ArgSlotKind.IntReg, 1)] };
        Node result = ir.Raw(Op.Proj, VT.I64, call);
        ir.Raw(Op.Return, VT.None, result);
        return new(function, guard, refusal, next, owner, stale, call);
    }

    private static bool Capture(ReceiverFixture site, Function? callee = null, int nullSide = 0) =>
        (bool)ReceiverRule.GetMethod("Capture", All)!.Invoke(null,
            [site.Guard, nullSide, (Func<Node, int?>)(_ => Ignores(callee ?? ReceiverCallee()) ? 0 : null)])!;

    private static HirBuilder ReceiverBuilder(Node owner, HExpr expression)
    {
        var builder = (HirBuilder)RuntimeHelpers.GetUninitializedObject(typeof(HirBuilder));
        var semantics = typeof(HirBuilder).GetField("_sem", All)!;
        var values = (IDictionary)Activator.CreateInstance(semantics.FieldType)!;
        Type valueType = typeof(HirBuilder).Assembly.GetType("Rewind.Analysis.Recover.SVal", true)!;
        values[owner] = Activator.CreateInstance(valueType, All, null, [expression], null)!;
        semantics.SetValue(builder, values);
        var model = (Il2CppModel)RuntimeHelpers.GetUninitializedObject(typeof(Il2CppModel));
        Backing(model, "Sigs", Sigs); Set(builder, "_m", model);
        return builder;
    }

    private static Node? ReceiverFor(ReceiverFixture site, HExpr expression, TypeSig expected, int position = 0) =>
        (Node?)typeof(HirBuilder).GetMethod("CheckedReceiverFor", All)!.Invoke(
            ReceiverBuilder(site.Owner, expression), [site.Call, position, expected]);

    private static void ClosureReceivers()
    {
        foreach (RegisterModel registers in new[] { RegisterModel.Arm64, RegisterModel.Win64 })
        {
            Check(Ignores(ReceiverCallee(registers: registers)), registers.Name + ": overwritten incoming receiver is proved unused");
            Check(!Ignores(ReceiverCallee(reads: true, registers: registers)), registers.Name + ": actual receiver read prevents substitution");
        }
        var unsupported = ReceiverCallee(); unsupported.Problems.Add("unsupported instruction");
        Check(!Ignores(unsupported), "incomplete native lifting never proves unused this");
        Check(!Ignores(new Function { Regs = RegisterModel.Arm64 }), "missing native body never proves unused this");

        var ownerType = Define("ServiceOwner", false);
        var closureType = Define("CapturedCallback", false, ("owner", ownerType.Sig));
        HExpr captured = Field(new HArg(-1) { Type = closureType.Sig }, closureType.Fields[0], ownerType.Sig);
        foreach (bool previous in new[] { false, true })
        {
            var site = ReceiverSite(previous);
            Check(Capture(site), "null-checked owner survives a stale " + (previous ? "return value" : "closure") + " in x0");
            Check(ReferenceEquals(site.Call.In[0], site.Stale), "native ABI input remains available as evidence");
            Check(ReferenceEquals(ReceiverFor(site, captured, ownerType.Sig), site.Owner),
                "managed call selects the typed captured owner without a cast");
            Node branch = site.Guard.Terminator!;
            branch.Op = Op.Jump; branch.In = [];
            site.Guard.Succs.Clear(); site.Guard.Succs.Add(site.Next);
            site.Throw.Preds.Clear(); site.Function.Blocks.Remove(site.Throw);
            DeadCode.Run(site.Function);
            Check(!site.Owner.Dead && site.Guard.Nodes.Contains(site.Owner), "guard-only owner load survives normalizer dead-code cleanup");
            Check(ReferenceEquals(ReceiverFor(site, captured, ownerType.Sig), site.Owner),
                "typed recovery still selects the original load after cleanup");
            Check(site.Guard.Nodes.Count(n => ReferenceEquals(n, site.Owner)) == 1, "owner is captured once at its original read");
            ReceiverSemantics(captured, site, ownerType, previous);
        }
        var reverse = ReceiverSite(reversed: true);
        Check(Capture(reverse, nullSide: 1), "both branch polarities preserve the non-null edge");

        void Refuse(string name, Action<ReceiverFixture> change, Function? callee = null)
        {
            var site = ReceiverSite(); change(site);
            Check(!Capture(site, callee), name);
            Check(((CallInfo)site.Call.Aux!).Slots.All(s => s.Kind != ArgSlotKind.CheckedReceiver), "rejected proof adds no candidate");
        }
        Refuse("callee using this rejects a plausible adjacent owner", _ => { }, ReceiverCallee(reads: true));
        Refuse("call block with another predecessor has no unique guarded receiver", s => s.Next.Preds.Add(new Block()));
        Refuse("different exception scopes are not crossed", s => s.Next.Scope = 0);
        Refuse("intervening field read is not skipped", s => s.Next.Nodes.Insert(0,
            s.Function.NewNode(Op.Load, VT.I64, s.Next, s.Stale)));
        Refuse("intervening store is not skipped", s => s.Next.Nodes.Insert(0,
            s.Function.NewNode(Op.Store, VT.None, s.Next, s.Stale, s.Stale)));
        Refuse("intervening indirect call is not skipped", s => s.Next.Nodes.Insert(0,
            new Node { Op = Op.Call, Aux = new CallInfo { Indirect = true }, Block = s.Next }));
        Refuse("indirect target has no ignored-instance proof", s => ((CallInfo)s.Call.Aux!).Indirect = true);
        Refuse("intrinsic target has no managed receiver", s => ((CallInfo)s.Call.Aux!).Intrinsic = "probe");
        Refuse("comparison against nonzero is not a null check", s => s.Guard.Terminator!.In[0].In[1].Imm = 1);
        Refuse("wrong null-edge polarity is not accepted", s => s.Guard.Terminator!.In[0].Op = Op.CmpNe);
        Refuse("unresolved phi into the call block is not guessed", s => s.Next.Phis.Add(
            s.Function.NewNode(Op.Phi, VT.I64, s.Next, s.Owner)));
        Refuse("missing ABI receiver input is not guessed", s => ((CallInfo)s.Call.Aux!).Slots[0] = new ArgSlot(ArgSlotKind.Stack, 0));

        var typed = ReceiverSite(); Check(Capture(typed), "typed negative fixture has native guard evidence");
        var unrelated = Define("PreviousCallResult", false);
        Check(ReceiverFor(typed, new HArg(0) { Type = unrelated.Sig }, ownerType.Sig) == null,
            "unrelated reference cannot be cast into the declaring type");
        Check(ReceiverFor(typed, new HArg(0), ownerType.Sig) == null, "unknown type is insufficient receiver evidence");
        Check(ReceiverFor(typed, new HArg(0) { Type = Object }, ownerType.Sig) == null,
            "object static type is insufficient receiver evidence");
        Check(ReceiverFor(typed, new HArg(0) { Type = Int }, ownerType.Sig) == null, "value type is not a captured reference receiver");
        Check(ReceiverFor(typed, captured, ownerType.Sig, 1) == null, "evidence only applies to its proven ABI position");
        var derived = Define("DerivedOwner", false); derived.BaseType = ownerType.Sig;
        Check(ReferenceEquals(ReceiverFor(typed, new HArg(0) { Type = derived.Sig }, ownerType.Sig), typed.Owner),
            "a proven subclass receiver retains its actual identity");
        Check(!Capture(typed), "the same guard is not attached twice");
        typed.Call.In = [.. typed.Call.In, typed.Owner];
        ((CallInfo)typed.Call.Aux!).Slots.Add(new ArgSlot(ArgSlotKind.CheckedReceiver, 0));
        Check(ReceiverFor(typed, captured, ownerType.Sig) == null, "multiple candidate receivers are rejected");
        Cases.Add("omitted instance registers: typed closure owner, raw callee proof, guard lifetime, null and effect order");
    }

    private sealed class ReceiverState
    {
        public object? Owner;
        public object Closure = new(), Previous = new(), Service = new();
        public List<string> Events = [];
    }

    private static void ReceiverSemantics(HExpr captured, ReceiverFixture site, TypeDef ownerType, bool previous)
    {
        // The machine body ignores x0, but the caller checks the captured owner before reaching it.
        // The recovered managed call must reproduce that check and one field evaluation, including failures.
        foreach (bool isNull in new[] { false, true })
        foreach (bool throws in new[] { false, true })
        {
            object owner = new(), service = new();
            var native = new ReceiverState { Owner = isNull ? null : owner, Service = service };
            var managed = new ReceiverState { Owner = isNull ? null : owner, Service = service };
            var getter = new MethodDef { Name = "GetService", DeclaringType = ownerType, Flags = 1, ReturnType = Object };
            Node? selected = ReceiverFor(site, captured, ownerType.Sig);
            HExpr emittedReceiver = ReferenceEquals(selected, site.Owner) ? captured : new HArg(0) { Type = Object };
            var recoveredCall = new HCall { Method = getter, This = emittedReceiver, Arguments = [], Type = Object };
            object? Body(ReceiverState state)
            {
                state.Events.Add("service-body");
                if (throws) throw new ArithmeticException();
                return state.Service;
            }
            object? Evaluate(HExpr value, ReceiverState state)
            {
                switch (value)
                {
                    case HArg { Index: -1 }: return state.Closure;
                    case HArg: return previous ? state.Previous : state.Closure;
                    case HField field:
                        if (!ReferenceEquals(Evaluate(field.Object!, state), state.Closure)) throw new InvalidCastException();
                        state.Events.Add("read-owner");
                        return state.Owner;
                    case HCall call:
                        object? receiver = Evaluate(call.This!, state);
                        if (receiver == null) throw new NullReferenceException();
                        if (!ReferenceEquals(receiver, state.Owner)) throw new InvalidCastException();
                        return Body(state);
                    default: throw new InvalidOperationException("unexpected receiver expression");
                }
            }
            object? Run(ReceiverState state, bool recovered)
            {
                if (previous) state.Events.Add("previous-effect");
                object? result;
                if (recovered) result = Evaluate(recoveredCall, state);
                else
                {
                    // Original native caller: load and test owner; the callee ignores stale x0.
                    state.Events.Add("read-owner");
                    if (state.Owner == null) throw new NullReferenceException();
                    result = Body(state);
                }
                state.Events.Add("continuation");
                return result;
            }
            (object? Value, Type? Error) Outcome(ReceiverState state, bool recovered)
            {
                try { return (Run(state, recovered), null); }
                catch (Exception e) when (e is NullReferenceException or ArithmeticException or InvalidCastException) { return (null, e.GetType()); }
            }
            var before = Outcome(native, false); var after = Outcome(managed, true);
            Check(ReferenceEquals(before.Value, after.Value) && before.Error == after.Error,
                "receiver recovery preserves service identity and exception type");
            Check(native.Events.SequenceEqual(managed.Events), "null and callee exceptions precede continuation without extra owner reads");
            if (isNull) Check(!managed.Events.Contains("service-body"), "null owner throws before the ignored-this body");
        }
    }
}
