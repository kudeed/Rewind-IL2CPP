using Rewind.Analysis.Abi;
using Rewind.Analysis.Ir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    private readonly Dictionary<(ulong Address, int Register), bool> _ignoredReceivers = [];

    /// <summary>
    /// Only a uniquely identified, ordinary reference-type instance method is considered. Inspect its raw
    /// native function, before any normalization could erase uses of this. Unknown code, shared identities,
    /// generics, constructors, virtual/base calls and native forwarded implementations remain unproved.
    /// </summary>
    private int? IgnoredReceiverPosition(Node call)
    {
        if (call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info) return null;
        CallTarget target = program.Resolve(info.Target);
        if (target.Helper != null || target.Forwarded || target.Insts.Count != 0 || target.Methods is not [var method] ||
            method.Address != info.Target || method.IsStatic || method.IsVirtual || method.Name == ".ctor" ||
            method.GenericParameters.Length != 0 || method.DeclaringType.GenericParameters.Length != 0 ||
            method.DeclaringType.IsValueType)
            return null;
        MethodAbi abi = program.Abi.For(method, [], []);
        if (!abi.Known || abi.This is not { Pass: PassKind.Integer, Type: { IsValueType: false }, Position: var position })
            return null;
        int slot = _fn.Regs.IntRegisterOf(position);
        if (slot < 0 || slot >= _fn.Regs.IntArgs.Length) return null;
        int register = _fn.Regs.IntArgs[slot];
        var key = (info.Target, register);
        if (!_ignoredReceivers.TryGetValue(key, out bool ignores))
        {
            // A new lifter has its own mutable state; this never recursively runs normalization.
            try
            {
                ignores = ReceiverRecovery.DoesNotReadReceiver(program.NewLifter().Lift(info.Target), register);
            }
            catch (Exception e) when (e is not OutOfMemoryException and not StackOverflowException)
            {
                ignores = false;
            }
            _ignoredReceivers[key] = ignores;
        }
        return ignores ? position : null;
    }
}
