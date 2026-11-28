using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    private sealed record RuntimeInvokerPlan(SMethod Method, Node Receiver, HExpr[] Arguments,
        TypeSig DeclaringType, TypeSig ReturnType, HExpr? ReturnLocation);
    private sealed record RuntimeMarshalProof(Node Phi, Node Read, Block Guard, SRuntimeBuffer Buffer);

    private readonly Dictionary<Node, RuntimeInvokerPlan> _runtimeInvokers = [];
    private readonly HashSet<Node> _runtimeInvokerStores = [];
    private readonly HashSet<Block> _runtimeMarshalGuards = [];

    private static bool SameRuntimeMethod(SMethod first, MethodDef method, MethodInst? instance) =>
        ReferenceEquals(first.Method, method) &&
        (first.Inst?.ClassArguments ?? []).Select(t => t.Key).SequenceEqual((instance?.ClassArguments ?? []).Select(t => t.Key)) &&
        (first.Inst?.MethodArguments ?? []).Select(t => t.Key).SequenceEqual((instance?.MethodArguments ?? []).Select(t => t.Key));

    // Only an exact full-width store after the last call can define a cell of this invocation's address
    // table. Partial/overlapping writes and an unknown address invalidate the proof.
    private Node? RuntimeInvokerCell(Node call, int offset, int bytes)
    {
        if (call.Block is not { } block) return null;
        for (int i = block.Nodes.IndexOf(call) - 1; i >= 0; i--)
        {
            Node previous = block.Nodes[i];
            if (previous.Dead) continue;
            if (previous.Op is Op.Call or Op.TailCall) return null;
            if (previous.Op != Op.Store) continue;
            if (!IsFrameAddress(previous.In[0], out int at)) return null;
            int size = previous.In[1].Type.Bytes();
            if ((long)at < (long)offset + bytes && (long)offset < (long)at + size)
                return at == offset && size == bytes ? previous : null;
        }
        return null;
    }

    private RuntimeMarshalProof? RuntimeMarshal(Node phi, TypeSig expected)
    {
        if (phi.Op != Op.Phi || phi.In.Length != 2 || phi.Block is not { Preds.Count: 2 } join) return null;
        for (int direct = 0; direct < 2; direct++)
        {
            Node address = phi.In[direct], read = phi.In[1 - direct];
            Block guard = join.Preds[direct], reference = join.Preds[1 - direct];
            if (read is not { Op: Op.Load, Type: VT.I64 } || !ReferenceEquals(read.In[0], address) ||
                Eval(address) is not SRuntimeBuffer buffer || buffer.Type.Key != expected.Key ||
                guard.Scope != join.Scope || reference.Scope != join.Scope ||
                guard.Succs.Count != 2 || !ReferenceEquals(guard.Succs[0], join) || !ReferenceEquals(guard.Succs[1], reference) ||
                reference.Preds.Count != 1 || !ReferenceEquals(reference.Preds[0], guard) ||
                reference.Succs.Count != 1 || !ReferenceEquals(reference.Succs[0], join) ||
                reference.Nodes.Any(n => !n.Dead && !ReferenceEquals(n, read) && n.Op != Op.Jump) ||
                !_uses.TryGetValue(read, out var readUsers) || readUsers.Any(n => !ReferenceEquals(n, phi)) ||
                join.Phis.Any(p => !p.Dead && !ReferenceEquals(p, phi) &&
                    (p.In.Length != 2 || !Normalizer.SameValue(p.In[0], p.In[1]))))
                continue;
            if (guard.Terminator is not { Op: Op.Branch } branch ||
                branch.In[0] is not { Op: Op.CmpLtS } condition || !condition.In[1].IsConstValue(0) ||
                condition.In[0] is not { Op: Op.Load, Type: VT.I32 } flags) continue;
            AddressParts field = Decompose(flags.In[0]);
            if (field.BaseSem is not SKlass klass || klass.Type.Key != expected.Key || field.Index != null ||
                field.Offset != _p.Klass.ByvalArg + _ptr) continue;
            // Il2CppType's bit 31 says valuetype: true keeps &T, false reads the reference held there.
            // Both paths therefore pass the same managed T, not a guessed pointer-sized value.
            return new RuntimeMarshalProof(phi, read, guard, buffer);
        }
        return null;
    }

    private void PlanRuntimeInvokers()
    {
        if (!_abi.UsesFullySharedRuntime) return;
        foreach (Block block in _cfg.ReversePostOrder)
            foreach (Node call in block.Nodes)
            {
                if (call.Dead || call.Op != Op.Call || call.Aux is not CallInfo { Indirect: true, NoReturn: false } ||
                    Eval(call.In[0]) is not SMethodInvoker invoker ||
                    IntAt(call, 0) is not { } codeNode || Eval(codeNode) is not SMethodCode code ||
                    IntAt(call, 1) is not { } infoNode || Eval(infoNode) is not SMethod info ||
                    !SameRuntimeMethod(invoker.Method, code.Method, code.Inst) ||
                    !SameRuntimeMethod(invoker.Method, info.Method, info.Inst) ||
                    IntAt(call, 2) is not { } receiver ||
                    IntAt(call, 3) is not { } table || !IsFrameAddress(table, out int tableAt))
                    continue;

                MethodDef method = info.Method;
                if (method.IsStatic || method.DeclaringType.IsValueType || method.Name == ".ctor") continue;
                TypeSig[] ca = info.Inst?.ClassArguments ?? [], ma = info.Inst?.MethodArguments ?? [];
                TypeSig declaring = ca.Length == 0 ? method.DeclaringType.Sig : _m.Sigs.GenericInst(method.DeclaringType, ca);
                if (Peek(receiver) is not SVal { Type: { } receiverType } || !IsAssignable(receiverType, declaring)) continue;
                TypeSig returned = _m.Sigs.Substitute(method.ReturnType, ca, ma);
                bool isVoid = returned is PrimitiveSig { Element: Il2CppTypeEnum.Void };
                if (!isVoid && returned is not GenericParamSig) continue;

                var arguments = new HExpr[method.Parameters.Length];
                var stores = new List<Node>();
                var marshals = new List<RuntimeMarshalProof>();
                bool valid = true;
                for (int i = 0; i < arguments.Length; i++)
                {
                    TypeSig type = _m.Sigs.Substitute(method.Parameters[i].Type, ca, ma);
                    if (RuntimeInvokerCell(call, tableAt + i * _ptr, _ptr) is not { } store)
                    { valid = false; break; }
                    stores.Add(store);
                    Node argument = store.In[1];
                    if (type is GenericParamSig)
                    {
                        RuntimeMarshalProof? proof = RuntimeMarshal(argument, type);
                        if (proof == null) { valid = false; break; }
                        arguments[i] = new HLocal(proof.Buffer.Variable) { Type = type };
                        marshals.Add(proof);
                    }
                    else if (type is PrimitiveSig && !IsReference(type) &&
                        _p.Layouts.SizeOf(type) is { Known: true, Size: > 0 and <= 8 } size &&
                        IsFrameAddress(argument, out int at) && RuntimeInvokerCell(call, at, size.Size) != null &&
                        LocationOf(argument, type) is { } location && location.Type?.Key == type.Key)
                        arguments[i] = location;
                    else { valid = false; break; }
                }
                HExpr? destination = null;
                if (valid && !isVoid)
                {
                    if (IntAt(call, 4) is not { } result || Eval(result) is not SRuntimeBuffer buffer ||
                        buffer.Type.Key != returned.Key ||
                        RuntimeInvokerCell(call, tableAt + arguments.Length * _ptr, _ptr) is not { } returnCell ||
                        !Normalizer.SameValue(returnCell.In[1], result))
                        valid = false;
                    else
                    {
                        destination = new HLocal(buffer.Variable) { Type = returned };
                        stores.Add(returnCell);
                    }
                }
                if (!valid || marshals.Any(proof =>
                    !_uses.TryGetValue(proof.Phi, out var uses) ||
                    uses.Any(use => !ReferenceEquals(use, call) && !stores.Contains(use))))
                    continue;

                _runtimeInvokers[call] = new RuntimeInvokerPlan(info, receiver, arguments, declaring, returned, destination);
                foreach (Node store in stores) _runtimeInvokerStores.Add(store);
                foreach (RuntimeMarshalProof proof in marshals)
                {
                    if (_phiVar.Remove(proof.Phi, out HVar? previous))
                    {
                        _phiOfVar.Remove(previous);
                        _h.Locals.Remove(previous);
                    }
                    var semantic = new SRuntimeMarshal(proof.Buffer);
                    _sem[proof.Phi] = semantic;
                    _sem[proof.Read] = semantic;
                    _runtimeMarshalGuards.Add(proof.Guard);
                }
            }
    }

    private bool TryEmitRuntimeInvoker(Node call)
    {
        if (!_runtimeInvokers.TryGetValue(call, out RuntimeInvokerPlan? plan)) return false;
        var invoke = new HCall
        {
            Method = plan.Method.Method, DeclaringType = plan.DeclaringType,
            MethodArguments = plan.Method.Inst?.MethodArguments ?? [],
            This = Value(plan.Receiver), Arguments = plan.Arguments, Type = plan.ReturnType,
            // This entry invokes exactly the method whose native code and metadata were both checked.
            Virtual = false
        };
        if (plan.ReturnLocation != null) Emit(new HAssign(plan.ReturnLocation, invoke), call.Addr);
        else Emit(new HEval(invoke), call.Addr);
        _h.Notes.Add($"fully shared invoker recovered at 0x{call.Addr:X}: {plan.Method.Method.Name}");
        return true;
    }
}
