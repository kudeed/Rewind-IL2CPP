using Iced.Intel;
using Rewind.Analysis.Abi;
using Rewind.Binary;
using Rewind.Model;
using Decoder = Iced.Intel.Decoder;

namespace Rewind.Analysis.Runtime;

/// <summary>A function the method tables do not list, identified as a private copy of a managed method.</summary>
public sealed class InlineCopy
{
    public MethodDef Method = null!;
    /// <summary>The instantiations callers were seen to name.</summary>
    public List<MethodInst> Insts = [];
    public int Sites;
}

/// <summary>
/// IL2CPP emits small methods marked for inlining a second time, next to their callers; when the C++ compiler
/// then declines to inline one, the copy survives as a function of its own that no table mentions. Shared
/// generic code, however, is always handed the descriptor of the method it stands for - so a caller that
/// passes a method descriptor in exactly the position where that method would expect its own thereby names
/// the function it calls. This finds those witnesses.
/// </summary>
public static partial class InlineCopyFinder
{
    private static readonly Register[] ArgumentRegisters = [Register.RCX, Register.RDX, Register.R8, Register.R9];
    private const ushort AggressiveInlining = 0x100;

    public static Dictionary<ulong, InlineCopy> Find(ProgramAnalysis program)
    {
        var result = new Dictionary<ulong, InlineCopy>();
        Il2CppModel model = program.Model;
        NativeImage image = model.Image;
        if (image.Arch == CpuArch.Arm64) return Choose(VotesArm64(program));
        if (image.Arch != CpuArch.X64) return result;

        var votes = new Dictionary<ulong, Dictionary<MethodDef, List<MethodInst?>>>();
        var slotOf = new ulong[32];
        var stackSlots = new ulong[4];

        foreach (FunctionRange f in image.FunctionTable)
        {
            int length = (int)(f.End - f.Start);
            if (length <= 0 || !image.TrySpan(f.Start, length, out ReadOnlySpan<byte> code)) continue;
            var decoder = Decoder.Create(64, new ByteArrayCodeReader(code.ToArray()), f.Start);
            Array.Clear(slotOf);
            Array.Clear(stackSlots);
            while (decoder.IP < f.End)
            {
                decoder.Decode(out Instruction ins);
                if (ins.IsInvalid) break;

                if (ins.FlowControl == FlowControl.Call && ins.Op0Kind == OpKind.NearBranch64)
                {
                    ulong target = ins.NearBranchTarget;
                    CallTarget known = program.Resolve(target);
                    if (!known.IsManaged && known.Helper == null)
                    {
                        for (int position = 0; position < 8; position++)
                        {
                            ulong slot = position < 4 ? slotOf[Index(ArgumentRegisters[position])] : stackSlots[position - 4];
                            if (slot == 0 || model.ResolveUsageSlot(slot) is not { Method: { } method } usage) continue;
                            if (usage.Kind is not (UsageKind.MethodDef or UsageKind.MethodRef)) continue;
                            // Only methods marked for aggressive inlining get such copies. (This also keeps a
                            // method pointer handed to a delegate constructor from being mistaken for a witness.)
                            if ((method.ImplFlags & AggressiveInlining) == 0) continue;
                            MethodInst? inst = usage.MethodInst;
                            MethodAbi abi = inst != null ? program.Abi.For(inst) : program.Abi.For(method, [], []);
                            // The descriptor must sit exactly where this method takes its own.
                            if (abi.Params.Count == 0 || abi.Params[^1].Role != ParamRole.MethodInfo || abi.Params[^1].Position != position) continue;
                            if (!votes.TryGetValue(target, out var byMethod)) votes[target] = byMethod = [];
                            if (!byMethod.TryGetValue(method, out List<MethodInst?>? list)) byMethod[method] = list = [];
                            list.Add(inst);
                        }
                    }
                }

                // Track which metadata slot a register was loaded from; anything else written to it forgets that.
                // Only general-purpose registers are tracked: other 64-bit registers (control, debug, MMX - in bytes
                // that decode as `mov rax, cr0` and the like) have no place in the table.
                if (ins.Mnemonic == Mnemonic.Mov && ins.Op0Kind == OpKind.Register && ins.Op0Register.IsGPR64())
                {
                    int destination = Index(ins.Op0Register);
                    if (ins.Op1Kind == OpKind.Memory && ins.IsIPRelativeMemoryOperand) slotOf[destination] = ins.IPRelativeMemoryAddress;
                    else if (ins.Op1Kind == OpKind.Register && ins.Op1Register.IsGPR64()) slotOf[destination] = slotOf[Index(ins.Op1Register)];
                    else slotOf[destination] = 0;
                }
                else if (ins.Mnemonic == Mnemonic.Mov && ins.Op0Kind == OpKind.Memory && ins.MemoryBase == Register.RSP && ins.MemoryIndex == Register.None &&
                         ins.Op1Kind == OpKind.Register && ins.Op1Register.IsGPR64())
                {
                    long offset = (long)ins.MemoryDisplacement64 - 0x20;
                    if (offset is >= 0 and < 32 && offset % 8 == 0) stackSlots[offset / 8] = slotOf[Index(ins.Op1Register)];
                }
                else if (ins.OpCount > 0 && ins.Op0Kind == OpKind.Register && ins.Mnemonic is not (Mnemonic.Cmp or Mnemonic.Test or Mnemonic.Push))
                {
                    Register full = ins.Op0Register.GetFullRegister();
                    if (full is >= Register.RAX and <= Register.R15) slotOf[Index(full)] = 0;
                }

                if (ins.FlowControl != FlowControl.Next)
                {
                    // Past a call the argument registers are gone; past a jump nothing is known.
                    if (ins.FlowControl == FlowControl.Call || ins.FlowControl == FlowControl.IndirectCall)
                    {
                        foreach (Register r in (Register[])[Register.RAX, Register.RCX, Register.RDX, Register.R8, Register.R9, Register.R10, Register.R11])
                            slotOf[Index(r)] = 0;
                    }
                    else Array.Clear(slotOf);
                    Array.Clear(stackSlots);
                }
            }
        }

        return Choose(votes);
    }

    /// <summary>The method the callers of each function agree they are calling (four in five of them at least).</summary>
    private static Dictionary<ulong, InlineCopy> Choose(Dictionary<ulong, Dictionary<MethodDef, List<MethodInst?>>> votes)
    {
        var result = new Dictionary<ulong, InlineCopy>();
        foreach (var (target, byMethod) in votes)
        {
            int total = byMethod.Values.Sum(v => v.Count);
            var (method, sites) = byMethod.OrderByDescending(kv => kv.Value.Count).Select(kv => (kv.Key, kv.Value)).First();
            // Callers must agree on what they are calling.
            if (sites.Count * 5 < total * 4) continue;
            var copy = new InlineCopy { Method = method, Sites = sites.Count };
            foreach (MethodInst? inst in sites)
                if (inst != null && !copy.Insts.Contains(inst))
                    copy.Insts.Add(inst);
            result[target] = copy;
        }
        return result;
    }

    private static int Index(Register register) => register.GetFullRegister() - Register.RAX;
}
