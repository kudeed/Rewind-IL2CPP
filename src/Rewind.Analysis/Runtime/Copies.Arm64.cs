using System.Buffers.Binary;
using System.Security.Cryptography;
using Rewind.Analysis.Abi;
using Rewind.Analysis.Arm64;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Runtime;

public static partial class CopyMatcher
{
    /// <summary>
    /// The A64 form of <see cref="Describe"/>: instruction words with the fields that say where things are
    /// blanked, and what they refer to added by identity - the address itself for what is shared (classes,
    /// strings, constants, the GOT), the order of first use for a variable of the function's own.
    /// </summary>
    private static Body? DescribeArm64(ProgramAnalysis program, IncrementalHash hash, ulong address)
    {
        NativeImage image = program.Model.Image;
        A64Cfg cfg = A64Cfg.Build(program.Context, address);
        if (cfg.Blocks.Count == 0) return null;
        var inside = new HashSet<ulong>();
        foreach (A64Block block in cfg.Blocks)
            foreach (A64Instruction ins in block.Instructions)
                inside.Add(ins.Address);

        var callees = new List<ulong>();
        Dictionary<ulong, int>? privates = null;
        Span<byte> word = stackalloc byte[4];
        Span<byte> note = stackalloc byte[16];
        int count = 0;
        foreach (A64Block block in cfg.Blocks.OrderBy(b => b.Start))
        {
            var pages = new Dictionary<byte, ulong>();
            foreach (A64Instruction ins in block.Instructions)
            {
                if (ins.IsInvalid) return null;
                BinaryPrimitives.WriteUInt32LittleEndian(note, (uint)(ins.Address - address));
                hash.AppendData(note[..4]);
                uint w = ins.Word;
                byte tag = 0;
                ulong identity = 0;
                void Refer(ulong target)
                {
                    ImageSection? section = image.SectionAt(target);
                    bool shared = section is not { IsWritable: true } || image.IsReadOnlyAfterLoad(target) ||
                                  program.Model.ResolveUsageSlot(target) != null || program.Defaults.Slots.ContainsKey(target);
                    if (shared)
                    {
                        tag = 1;
                        identity = target;
                    }
                    else
                    {
                        privates ??= [];
                        if (!privates.TryGetValue(target, out int ordinal)) privates[target] = ordinal = privates.Count;
                        tag = 2;
                        identity = (ulong)ordinal;
                    }
                }
                switch (ins.Op)
                {
                    case A64Op.B or A64Op.Bl:
                        if (!inside.Contains(ins.Target))
                        {
                            w &= 0xFC000000;
                            callees.Add(ins.Target);
                            tag = 4;
                        }
                        break;
                    case A64Op.BCond or A64Op.Cbz or A64Op.Cbnz:
                        if (!inside.Contains(ins.Target)) { w &= 0xFF00001F; callees.Add(ins.Target); tag = 4; }
                        break;
                    case A64Op.Tbz or A64Op.Tbnz:
                        if (!inside.Contains(ins.Target)) { w &= 0xFFF8001F; callees.Add(ins.Target); tag = 4; }
                        break;
                    case A64Op.Adr:
                        w &= 0x9F00001F;
                        Refer(ins.Target);
                        break;
                    case A64Op.Adrp:
                        w &= 0x9F00001F;
                        break;
                    case A64Op.LdrLit:
                        w &= 0xFF00001F;
                        Refer(ins.Target);
                        break;
                    case A64Op.AddImm when !ins.SetFlags && ins.Rn < 31 && pages.TryGetValue(ins.Rn, out ulong page):
                        w &= 0xFFC003FF;
                        Refer(page + (ulong)ins.Imm);
                        break;
                    case A64Op.Ldr or A64Op.Str when ins.Mode == A64Mode.Offset && ins.Rn < 31 && (w & 0x3B000000) == 0x39000000 &&
                                                     pages.TryGetValue(ins.Rn, out ulong slotPage):
                        w &= 0xFFC003FF;
                        Refer(slotPage + (ulong)ins.Imm);
                        break;
                }
                if (ins.Op == A64Op.Adrp) pages[ins.Rd] = ins.Target;
                else
                    foreach (byte r in pages.Keys.ToList())
                        if (A64Cfg.Writes(ins, r)) pages.Remove(r);
                BinaryPrimitives.WriteUInt32LittleEndian(word, w);
                hash.AppendData(word);
                if (tag != 0)
                {
                    note[0] = tag;
                    BinaryPrimitives.WriteUInt64LittleEndian(note[1..], identity);
                    hash.AppendData(note[..9]);
                }
                count++;
            }
        }
        return new Body { Code = Finish(hash), Callees = callees.ToArray(), Instructions = count };
    }
}

public static partial class InlineCopyFinder
{
    /// <summary>
    /// The A64 form of <see cref="Find"/>: which metadata slot each argument register was loaded from (through
    /// ADRP, the GOT and the slot itself), at every call of a function the tables do not list.
    /// </summary>
    private static Dictionary<ulong, Dictionary<MethodDef, List<MethodInst?>>> VotesArm64(ProgramAnalysis program)
    {
        var votes = new Dictionary<ulong, Dictionary<MethodDef, List<MethodInst?>>>();
        Il2CppModel model = program.Model;
        NativeImage image = model.Image;
        var constant = new ulong[32];
        var slotOf = new ulong[32];
        foreach (FunctionRange f in image.FunctionTable)
        {
            Array.Clear(constant);
            Array.Clear(slotOf);
            for (ulong at = f.Start; at + 4 <= f.End && image.IsMapped(at, 4); at += 4)
            {
                A64Instruction ins = A64Decoder.Decode(image.U32(at), at);
                if (ins.IsInvalid) break;
                if (ins.Op == A64Op.Bl)
                {
                    CallTarget known = program.Resolve(ins.Target);
                    if (!known.IsManaged && known.Helper == null)
                        for (int position = 0; position < 8; position++)
                        {
                            ulong slot = slotOf[position];
                            if (slot == 0 || model.ResolveUsageSlot(slot) is not { Method: { } method } usage) continue;
                            if (usage.Kind is not (UsageKind.MethodDef or UsageKind.MethodRef)) continue;
                            if ((method.ImplFlags & AggressiveInlining) == 0) continue;
                            MethodInst? inst = usage.MethodInst;
                            MethodAbi abi = inst != null ? program.Abi.For(inst) : program.Abi.For(method, [], []);
                            if (abi.Params.Count == 0 || abi.Params[^1].Role != ParamRole.MethodInfo || abi.Params[^1].Position != position) continue;
                            if (!votes.TryGetValue(ins.Target, out var byMethod)) votes[ins.Target] = byMethod = [];
                            if (!byMethod.TryGetValue(method, out List<MethodInst?>? list)) byMethod[method] = list = [];
                            list.Add(inst);
                        }
                }
                switch (ins.Op)
                {
                    case A64Op.Adrp or A64Op.Adr:
                        constant[ins.Rd] = ins.Target;
                        slotOf[ins.Rd] = 0;
                        continue;
                    case A64Op.AddImm when !ins.SetFlags && ins.Rn < 31 && ins.Rd < 31 && constant[ins.Rn] != 0:
                        constant[ins.Rd] = constant[ins.Rn] + (ulong)ins.Imm;
                        slotOf[ins.Rd] = 0;
                        continue;
                    case A64Op.Ldr when !ins.Vector && ins.Size == 8 && ins.Mode == A64Mode.Offset && ins.Rn < 31 && ins.Rd < 31 && constant[ins.Rn] != 0:
                    {
                        ulong from = constant[ins.Rn] + (ulong)ins.Imm;
                        // A GOT entry holds the address of a global (a slot); a slot holds what it was set to.
                        if (image.IsReadOnlyAfterLoad(from)) { constant[ins.Rd] = image.U64(from); slotOf[ins.Rd] = 0; }
                        else { constant[ins.Rd] = 0; slotOf[ins.Rd] = model.ResolveUsageSlot(from) != null ? from : 0; }
                        continue;
                    }
                    case A64Op.Orr when ins.Rn == A64Instruction.Zr && ins.Amount == 0 && ins.Is64 && ins.Rd < 31 && ins.Rm < 31:
                        constant[ins.Rd] = constant[ins.Rm];
                        slotOf[ins.Rd] = slotOf[ins.Rm];
                        continue;
                    case A64Op.Bl or A64Op.Blr:
                        for (int r = 0; r <= 18; r++) { constant[r] = 0; slotOf[r] = 0; }
                        continue;
                    case A64Op.B or A64Op.Br or A64Op.Ret or A64Op.BCond or A64Op.Cbz or A64Op.Cbnz or A64Op.Tbz or A64Op.Tbnz:
                        Array.Clear(constant);
                        Array.Clear(slotOf);
                        continue;
                }
                for (byte r = 0; r < 31; r++)
                    if ((constant[r] != 0 || slotOf[r] != 0) && A64Cfg.Writes(ins, r)) { constant[r] = 0; slotOf[r] = 0; }
            }
        }
        return votes;
    }
}
