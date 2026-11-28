using Rewind.Analysis.Abi;
using Rewind.Analysis.Arm64;
using Rewind.Analysis.Ir;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Passes;

/// <summary>Restores only a proven unused direct receiver before its dead metadata phis become managed values.</summary>
public static class MetadataReceivers
{
    public static int Run(ProgramAnalysis program, Function fn, MethodDef caller, MethodAbi abi, Action<string> note)
    {
        var model = program.Model;
        if (model.Image.Arch != CpuArch.Arm64 || fn.TryRegions.Count != 0 ||
            caller.IsStatic || caller.IsConstructor || caller.IsGenericDefinition ||
            caller.DeclaringType.IsValueType || caller.DeclaringType.IsGenericDefinition ||
            abi.This is not { Position: 0, Pass: PassKind.Integer } ||
            !fn.Params.TryGetValue(fn.Regs.IntArgs[0], out Node? incoming)) return 0;
        var proofs = new Dictionary<ulong, bool>();
        int changed = 0;
        foreach (Node call in fn.Blocks.SelectMany(b => b.Nodes))
        {
            if (call.Dead || call.Op is not (Op.Call or Op.TailCall) ||
                call.Aux is not CallInfo { Indirect: false, Intrinsic: null, NoReturn: false } info) continue;
            int receiver = info.Slots.FindIndex(s => s.Kind == ArgSlotKind.IntReg && s.Index == 0);
            if (receiver < 0 || receiver >= call.In.Length ||
                !OwnMetadataReceiverProof.IsExact(call.In[receiver], incoming, leaf =>
                    model.ResolveUsageSlot((ulong)leaf.Imm) is { Kind: UsageKind.TypeInfo, Type: TypeDefSig owner } &&
                    ReferenceEquals(owner.Definition, caller.DeclaringType)) ||
                !model.MethodsByAddress.TryGetValue(info.Target, out var methods) || methods.Count != 1 ||
                model.InstsByAddress.ContainsKey(info.Target)) continue;
            MethodDef callee = methods[0];
            if (callee.IsStatic || callee.IsConstructor || callee.IsVirtual || callee.IsAbstract || callee.IsGenericDefinition ||
                !ReferenceEquals(callee.DeclaringType, caller.DeclaringType) || callee.Address != info.Target ||
                program.RangeOf(info.Target) is not { } range) continue;
            if (!proofs.TryGetValue(info.Target, out bool unused))
            {
                unused = Arm64ReceiverProof.IsUnused(model.Image, range.Start, range.End);
                proofs[info.Target] = unused;
            }
            if (!unused) continue;
            call.In[receiver] = incoming;
            note($"receiver-independent same-owner metadata at 0x{call.Addr:X} to 0x{callee.Address:X}");
            changed++;
        }
        if (changed != 0) DeadCode.Run(fn);
        return changed;
    }
}
