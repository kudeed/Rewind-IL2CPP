using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Recover;

/// <summary>
/// A native compiler may omit an instance argument whose callee never reads it. The caller's adjacent
/// null check can still identify that receiver. Keep this as an extra, non-ABI input until managed types
/// are known, rather than interpreting a stale argument register as an object of the declaring class.
/// </summary>
internal static class ReceiverRecovery
{
    /// <summary>
    /// A deliberately strict native proof: the lifter never needed the entry value of this register.
    /// Merely finding it unused after guard/argument cleanup would not prove that the callee ignores it.
    /// </summary>
    internal static bool DoesNotReadReceiver(Function function, int register) =>
        register >= 0 && function.Blocks.Count != 0 && function.Problems.Count == 0 &&
        !function.Params.ContainsKey(register);

    /// <summary>
    /// Preserve the object of an actual null-throw guard for the immediately following direct call.
    /// The callback returns the instance argument's position only when its compiled body ignores it.
    /// No other entry into the call block, intervening memory access, store, call or control flow is allowed.
    /// </summary>
    internal static bool Capture(Block guard, int nullSide, Func<Node, int?> ignoredPosition)
    {
        if (nullSide is < 0 or > 1 || guard.Terminator is not { Op: Op.Branch, In: [var condition] } ||
            guard.Succs.Count != 2 || condition.Op is not (Op.CmpEq or Op.CmpNe) || condition.In.Length != 2 ||
            (condition.Op == Op.CmpEq ? 0 : 1) != nullSide)
            return false;
        Node left = condition.In[0], right = condition.In[1];
        Node? owner = right.IsConstValue(0) ? left : left.IsConstValue(0) ? right : null;
        if (owner == null || owner.IsConst || owner.Type is not (VT.I64 or VT.I32)) return false;

        Block next = guard.Succs[1 - nullSide];
        if (next.Scope != guard.Scope || next.Preds.Count != 1 || !ReferenceEquals(next.Preds[0], guard) ||
            next.Phis.Any(n => !n.Dead))
            return false;
        Node? call = next.Nodes.FirstOrDefault(n => !n.Dead && n.IsEffect);
        if (call is not { Op: Op.Call or Op.TailCall, Aux: CallInfo { Indirect: false, Intrinsic: null } info } ||
            info.Slots.Count != call.In.Length || info.Slots.Any(s => s.Kind == ArgSlotKind.CheckedReceiver) ||
            ignoredPosition(call) is not { } position ||
            !info.Slots.Any(s => s.Kind == ArgSlotKind.IntReg && s.Index == position))
            return false;

        call.In = [.. call.In, owner];
        info.Slots.Add(new ArgSlot(ArgSlotKind.CheckedReceiver, position));
        return true;
    }

    internal static Node? CheckedReceiver(Node call, int position)
    {
        if (call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info || info.Slots.Count != call.In.Length)
            return null;
        Node? found = null;
        for (int i = 0; i < info.Slots.Count; i++)
        {
            if (info.Slots[i] is not { Kind: ArgSlotKind.CheckedReceiver } slot || slot.Index != position) continue;
            if (found != null) return null;
            found = call.In[i];
        }
        return found;
    }
}
