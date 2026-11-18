using System.Security.Cryptography;
using Rewind.Analysis.Arm64;
using Rewind.Binary;

namespace Rewind.Analysis.Runtime;

public sealed partial class CodeIndex
{
    /// <summary>
    /// The A64 form of <see cref="Compute"/>: instruction words with every field that encodes a distance to other
    /// code or data blanked. Those are the offsets of branches out of the function, ADR/ADRP and literal loads,
    /// and the low 12 bits of an address an ADRP started (the ADD or load/store immediate that follows it).
    /// </summary>
    private FunctionCode? ComputeArm64(ulong address)
    {
        A64Cfg cfg = A64Cfg.Build(context, address);
        if (cfg.Blocks.Count == 0) return null;
        var inside = new HashSet<ulong>();
        foreach (A64Block block in cfg.Blocks)
            foreach (A64Instruction ins in block.Instructions)
                inside.Add(ins.Address);

        var result = new FunctionCode();
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        var tokens = new List<uint>();
        Span<byte> word = stackalloc byte[4];
        int total = 0;
        foreach (A64Block block in cfg.Blocks.OrderBy(b => b.Start))
        {
            // Registers holding an ADRP page, in this block.
            var pages = new Dictionary<byte, ulong>();
            foreach (A64Instruction ins in block.Instructions)
            {
                if (ins.IsInvalid) return null;
                uint w = ins.Word;
                switch (ins.Op)
                {
                    case A64Op.B or A64Op.Bl:
                        if (!inside.Contains(ins.Target))
                        {
                            w &= 0xFC000000;
                            result.Callees.Add(ins.Target);
                        }
                        break;
                    case A64Op.BCond or A64Op.Cbz or A64Op.Cbnz:
                        if (!inside.Contains(ins.Target)) w &= 0xFF00001F;
                        break;
                    case A64Op.Tbz or A64Op.Tbnz:
                        if (!inside.Contains(ins.Target)) w &= 0xFFF8001F;
                        break;
                    case A64Op.Adr:
                        w &= 0x9F00001F;
                        if (StringAt(ins.Target) is { } adrText) result.Names.Add(adrText);
                        break;
                    case A64Op.Adrp:
                        w &= 0x9F00001F;
                        break;
                    case A64Op.LdrLit:
                        w &= 0xFF00001F;
                        break;
                    case A64Op.AddImm when !ins.SetFlags && ins.Rn < 31 && pages.TryGetValue(ins.Rn, out ulong page):
                        w &= 0xFFC003FF;
                        if (StringAt(page + (ulong)ins.Imm) is { } text) result.Names.Add(text);
                        break;
                    case A64Op.Ldr or A64Op.Str when ins.Mode == A64Mode.Offset && ins.Rn < 31 && pages.TryGetValue(ins.Rn, out ulong slotPage) &&
                                                     (w & 0x3B000000) == 0x39000000:
                    {
                        w &= 0xFFC003FF;
                        ulong slot = slotPage + (ulong)ins.Imm;
                        if (ins.Op == A64Op.Ldr && _image.ImportSlots.TryGetValue(slot, out string? import)) result.Names.Add("import:" + import);
                        break;
                    }
                }
                // Track ADRP pages through to their first use (and forget them when the register changes).
                if (ins.Op == A64Op.Adrp) pages[ins.Rd] = ins.Target;
                else
                    foreach (byte r in pages.Keys.ToList())
                        if (A64Cfg.Writes(ins, r)) pages.Remove(r);

                System.Buffers.Binary.BinaryPrimitives.WriteUInt32LittleEndian(word, w);
                hash.AppendData(word);
                total += 4;
                tokens.Add(TokenArm64(ins));
            }
        }
        result.Shallow = new Fingerprint(total, BitConverter.ToUInt64(hash.GetHashAndReset()));
        result.Instructions = tokens.Count;
        result.Sketch = MakeSketch(tokens);
        return result;
    }

    /// <summary>What an A64 instruction does, without the registers and addresses that vary between builds.</summary>
    private static uint TokenArm64(in A64Instruction ins)
    {
        uint h = Mix(0x811C9DC5, (uint)ins.Op);
        h = Mix(h, (ins.Is64 ? 1u : 0u) | (ins.SetFlags ? 2u : 0u) | (ins.Vector ? 4u : 0u) | (ins.Signed ? 8u : 0u));
        h = Mix(h, ins.Size | (uint)ins.FpSize << 8 | (uint)ins.Mode << 16);
        if (ins.Op is A64Op.BCond or A64Op.Csel or A64Op.Csinc or A64Op.Csinv or A64Op.Csneg or A64Op.CcmpImm or A64Op.CcmpReg) h = Mix(h, ins.Cond);
        bool relative = ins.Op is A64Op.Adr or A64Op.Adrp or A64Op.LdrLit or A64Op.B or A64Op.Bl or A64Op.BCond or A64Op.Cbz or A64Op.Cbnz
            or A64Op.Tbz or A64Op.Tbnz;
        if (!relative && ins.Imm is >= 0 and < 0x800) h = Mix(h, (uint)ins.Imm);
        return h;
    }
}
