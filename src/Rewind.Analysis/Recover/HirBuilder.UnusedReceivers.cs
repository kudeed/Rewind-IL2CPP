using Rewind.Analysis.Abi;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>The proof is taken from the complete raw lift, never from IR whose arguments were pruned.</summary>
internal static class UnusedReceiverProof
{
    internal static bool Accepts(Function raw, ulong address, int register, MethodAbi abi, bool hasLandingPad, FunctionRange? range, NativeImage image)
    {
        if (range is not { Chained: false } bound || bound.Start != address || bound.End <= address ||
            raw.End < bound.End || raw.Blocks.Any(b => b.Start < bound.Start || b.End > bound.End) ||
            hasLandingPad || raw.Address != address || register < 0 || !abi.Known || raw.Blocks.Count == 0 ||
            raw.Problems.Count != 0 || raw.TryRegions.Count != 0 || raw.Blocks.Any(b => b.Scope != -1) ||
            !ReferenceEquals(raw.Regs, RegisterModel.Arm64) || !CompleteReturnControl(raw, image)) return false;
        if (!raw.Params.TryGetValue(register, out Node? entry)) return true;

        // A64Lifter.ReturnValues captures all possible return registers even for a void method. These are
        // not machine reads. Only the return lanes the actual ABI consumes can observe an incoming value.
        // Phi nodes are SSA plumbing; every other user, including speculative call inputs, is a rejection.
        bool Returned(int index) => abi.Return switch
        {
            ReturnKind.Void or ReturnKind.Buffer => false,
            ReturnKind.Integer or ReturnKind.StructInRegister => index == 0,
            ReturnKind.StructInRegisterPair => index is 0 or 3,
            ReturnKind.Float => index == 1,
            ReturnKind.Double => index is 1 or 2,
            ReturnKind.FloatAggregate => index is not (0 or 3), // conservatively keep every FP return lane
            _ => true,
        };
        Node[] nodes = raw.Blocks.SelectMany(b => b.Phis.Concat(b.Nodes)).ToArray();
        var pending = new Queue<Node>();
        var seen = new HashSet<Node>();
        pending.Enqueue(entry);
        while (pending.TryDequeue(out Node? value))
        {
            if (!seen.Add(value)) continue;
            foreach (Node user in nodes)
                for (int i = 0; i < user.In.Length; i++)
                {
                    if (!ReferenceEquals(user.In[i], value)) continue;
                    if (user.Op == Op.Phi) pending.Enqueue(user);
                    else if (user.Op != Op.Return || Returned(i)) return false;
                }
        }
        return true;
    }

    // The raw lifter represents RET as ReturnValues(), without its branch register. Validate those
    // control dependencies directly before treating any raw return input as ABI-dead. Register moves
    // into LR otherwise disappear as SSA aliases, and pointer-authenticating hints can have hidden inputs.
    private static bool CompleteReturnControl(Function raw, NativeImage image)
    {
        if (image.Arch != CpuArch.Arm64) return false;
        foreach (Block block in raw.Blocks)
        {
            if ((block.Start & 3) != 0 || (block.End & 3) != 0 || block.End < block.Start ||
                block.End - block.Start > int.MaxValue ||
                !image.TrySpan(block.Start, (int)(block.End - block.Start), out _)) return false;
            for (ulong at = block.Start; at < block.End; at += 4)
            {
                A64Instruction i = A64Decoder.Decode(image.U32(at), at);
                if (i.Op is A64Op.Invalid or A64Op.Unknown) return false;
                if (i.Op == A64Op.Ret && (i.Rn != 30 || i.Word != 0xD65F03C0)) return false;
                // Authenticated register branches have modifier registers not represented by the lifter.
                if (i.Op == A64Op.Br && (i.Word & 0xFFFFFC1F) != 0xD61F0000 ||
                    i.Op == A64Op.Blr && (i.Word & 0xFFFFFC1F) != 0xD63F0000) return false;
                if (i.Op == A64Op.Nop && i.Word != 0xD503201F &&
                    (i.Word & 0xFFFFFF3F) != 0xD503241F) return false; // ordinary NOP or BTI only
                // An address update is a GP write even when the load itself targets a vector register.
                if (i.Rn == 30 && i.Mode is A64Mode.PreIndex or A64Mode.PostIndex) return false;
                bool writesLr = A64Cfg.Writes(i, 30) ||
                    (i.Op is A64Op.Cas or A64Op.Casp) && i.Ra == 30;
                if (!writesLr || i.Op is A64Op.Bl or A64Op.Blr) continue;
                // Ordinary 64-bit loads restore LR. If their address or stored data derives from x0,
                // the raw use graph below sees that real memory operation and rejects it independently.
                if (i.Op is A64Op.Ldr or A64Op.Ldp && !i.Vector && i.Size == 8 && !i.Signed) continue;
                return false;
            }
        }
        return true;
    }

    // ContainsGenericParameter alone does not reject a bare generic TypeDefSig. Check the complete
    // signature form, including types nested in arrays or pointers, with a bounded recursive proof.
    internal static bool ClosedSignature(TypeSig type, int budget = 32)
    {
        if (budget <= 0) return false;
        return type switch
        {
            PrimitiveSig => true,
            TypeDefSig t => t.Definition.GenericParameters.Length == 0,
            GenericInstSig g => g.Arguments.Length == g.Definition.GenericParameters.Length &&
                g.Arguments.All(a => ClosedSignature(a, budget - 1)),
            SzArraySig a => ClosedSignature(a.ElementType, budget - 1),
            ArraySig a => ClosedSignature(a.ElementType, budget - 1),
            PointerSig p => ClosedSignature(p.ElementType, budget - 1),
            ByRefSig r => ClosedSignature(r.ElementType, budget - 1),
            _ => false,
        };
    }

    internal static bool ClosedTarget(CallTarget target, MethodDef method) =>
        target.Helper == null && !target.Forwarded && target.Insts.Count == 0 &&
        target.Methods.Count == 1 && ReferenceEquals(target.Methods[0], method) && method.Address != 0 &&
        !method.IsStatic && !method.IsVirtual && method.Name != ".ctor" &&
        (method.Flags & MethodDef.Abstract) == 0 && !method.DeclaringType.IsValueType &&
        !method.DeclaringType.IsInterface && method.GenericParameters.Length == 0 &&
        method.DeclaringType.GenericParameters.Length == 0 && ClosedSignature(method.ReturnType) &&
        method.Parameters.All(p => ClosedSignature(p.Type));
}

public sealed partial class HirBuilder
{
    private readonly Dictionary<(ulong Address, int Register), bool> _unusedNativeReceivers = [];

    private bool NativeReceiverUnused(MethodDef method, MethodAbi abi)
    {
        // This recovery is confined to the ABI/image form for which the raw-read proof is exercised.
        if (_m.Image.Arch != CpuArch.Arm64 || _m.Image.Format != ImageFormat.Elf ||
            !abi.Known || abi.This is not { Pass: PassKind.Integer, Position: var position }) return false;
        int slot = _fn.Regs.IntRegisterOf(position);
        if (slot < 0 || slot >= _fn.Regs.IntArgs.Length) return false;
        int register = _fn.Regs.IntArgs[slot];
        var key = (method.Address, register);
        if (_unusedNativeReceivers.TryGetValue(key, out bool unused)) return unused;
        try
        {
            // The raw A64 lift reconstructs catch regions, but may omit cleanup-only landing pads.
            // Reject both kinds rather than infer anything about an unvisited exception path.
            FunctionRange? range = _p.RangeOf(method.Address);
            bool landingPad = _m.Image is ElfImage elf && elf.ExceptionTableOf(method.Address) is { } table &&
                              table.CallSites.Any(c => c.LandingPad != 0);
            unused = range.HasValue && !landingPad && UnusedReceiverProof.Accepts(_p.NewLifter().Lift(method.Address),
                method.Address, register, abi, landingPad, range, _m.Image);
        }
        catch (Exception e) when (e is not OutOfMemoryException and not StackOverflowException)
        {
            unused = false;
        }
        return _unusedNativeReceivers[key] = unused;
    }

    /// <summary>
    /// A stale non-object in the this register is not the receiver of an instance method. For an exact,
    /// closed direct target, an unused entry register permits a receiver of the same declaring class to
    /// stand in its place. The current managed this is such a value even when null, because the resulting
    /// HCall explicitly retains the native direct-call semantics. Existing checked receivers take priority.
    /// </summary>
    private bool RecoverUnusedReceiver(Node call, MethodDef method, MethodAbi abi, TypeSig[] classArgs,
        TypeSig[] methodArgs, out HExpr? receiver, out bool direct)
    {
        receiver = null;
        direct = false;
        if (classArgs.Length != 0 || methodArgs.Length != 0 ||
            call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info || info.Target != method.Address ||
            info.Slots.Count != call.In.Length || info.Slots.Any(s => s.Kind == ArgSlotKind.CheckedReceiver) ||
            abi.This is not { Pass: PassKind.Integer, Type: { IsValueType: false } expected, Position: var position } ||
            !ReferenceEquals(expected, method.DeclaringType.Sig) ||
            !UnusedReceiverProof.ClosedTarget(_p.Resolve(info.Target), method)) return false;

        Node? old = IntAt(call, position);
        Sem? meaning = old == null ? null : Peek(old);
        HExpr? oldValue = meaning switch { SVal v => v.Expr, SHalf h => h.Whole, _ => null };
        TypeSig? actual = oldValue?.Type;
        // Ordinary typed receivers, wrapper objects and independently checked casts keep the existing policy.
        if (actual != null && (IsAssignable(actual, expected) || IsReferenceWrapper(actual))) return false;
        if (old != null && CheckedClassHere(old) is { } checkedType && IsAssignable(checkedType, expected)) return false;
        // A successful type-test fact is distinct from a throwing cast guard. Keep the real object
        // when that fact dominates this exact call, even if its stored expression is still base-typed.
        if (old != null && ReferenceEquals(_node, call) && _block != null && ReferenceEquals(call.Block, _block) &&
            _position.TryGetValue(call, out int at) && (uint)at < (uint)_block.Nodes.Count &&
            ReferenceEquals(_block.Nodes[at], call) &&
            TestedType(old) is { Definition: { IsInterface: false, IsValueType: false } } tested &&
            UnusedReceiverProof.ClosedSignature(tested) && IsAssignable(tested, expected)) return false;
        if (actual == null && old is not null && old.Op != Op.Undef && !old.IsConstValue(0)) return false;

        bool unused = NativeReceiverUnused(method, abi);
        bool ownClass = !_method.IsStatic && _method.Name != ".ctor" &&
            _method.GenericParameters.Length == 0 && _l.ClassArguments.Length == 0 && _l.MethodArguments.Length == 0 &&
            ReferenceEquals(_method.DeclaringType, method.DeclaringType) &&
            ReferenceEquals(_abi.This?.Type, expected);
        // Atoms were already evaluated. A pending ordinary call/allocation can be retained explicitly.
        // Other deferred expressions (notably nullable field/pointer reads) are not silently discarded;
        // existing generic "pure" folding is too broad to guarantee their exceptional effects here.
        bool atom = oldValue is HConst or HArg or HLocal;
        bool effect = meaning is SVal && (oldValue is HCall or HNewObject or HNewArray) && !IsPure(oldValue);
        bool noValue = old == null || old.Op == Op.Undef || old.IsConstValue(0);
        if (!unused || !ownClass || !(atom || effect || noValue))
        {
            Problem(UnkeptReceiver);
            receiver = new HConst(null, expected);
            return true;
        }

        // Even an HLocal can still hold deferred phi bookkeeping. Commit that read before replacing it;
        // Eval avoids manufacturing integer bits from a SHalf whose already-materialized whole is a struct.
        if (old != null && (atom || effect)) _ = Eval(old);
        // Keep a pending call/allocation before the managed arguments, exactly where evaluating the old
        // receiver would have executed it. Already materialized atoms need no extra evaluation statement.
        if (effect) Emit(new HEval(Value(old!)), call.Addr);
        receiver = new HArg(-1) { Type = expected };
        direct = true;
        return true;
    }
}
