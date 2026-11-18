using System.Buffers.Binary;
using System.Security.Cryptography;
using Iced.Intel;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Decoder = Iced.Intel.Decoder;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Finds functions that no table lists but that are, instruction for instruction, a listed method.
///
/// The C++ compiler keeps private copies of small methods next to their callers. Such a copy is compiled
/// from the same text as the method itself, so its machine code is the method's machine code: the same bytes
/// at the same offsets, referring to the same classes, strings and functions. Only two things differ - where
/// the copy sits, and which private "already initialized" flag it uses. Comparing everything else exactly
/// identifies the copy with certainty: a function that executes the same instructions on the same data does
/// the same thing, so a call to the copy is a call to the method.
///
/// A copy may call other copies, so identities are refined until they stop changing: two functions are the
/// same when their own code is the same and the functions they call are the same.
/// </summary>
public static partial class CopyMatcher
{
    private sealed class Body
    {
        public UInt128 Code;
        public ulong[] Callees = [];
        public int Instructions;
    }

    public sealed class Result
    {
        /// <summary>Unlisted function to the listed addresses whose code it equals.</summary>
        public Dictionary<ulong, ulong[]> Copies = [];
        public int Examined, Rounds;
    }

    private static UInt128 Finish(IncrementalHash hash)
    {
        Span<byte> digest = stackalloc byte[32];
        hash.GetHashAndReset(digest);
        return new UInt128(BinaryPrimitives.ReadUInt64LittleEndian(digest), BinaryPrimitives.ReadUInt64LittleEndian(digest[8..]));
    }

    private static Body? Describe(ProgramAnalysis program, IncrementalHash hash, ulong address, ulong imageSpan)
    {
        NativeImage image = program.Model.Image;
        X64Cfg cfg = X64Cfg.Build(program.Context, address);
        if (cfg.Blocks.Count == 0) return null;
        var inside = new HashSet<ulong>();
        foreach (RawBlock block in cfg.Blocks)
            foreach (Instruction ins in block.Instructions)
                inside.Add(ins.IP);

        var callees = new List<ulong>();
        Dictionary<ulong, int>? privates = null;
        Span<byte> bytes = stackalloc byte[16];
        Span<byte> note = stackalloc byte[16];
        int count = 0;
        foreach (RawBlock block in cfg.Blocks.OrderBy(b => b.Start))
        {
            foreach (Instruction decoded in block.Instructions)
            {
                if (decoded.IsInvalid) return null;
                int length = decoded.Length;
                if (!image.TrySpan(decoded.IP, length, out ReadOnlySpan<byte> raw)) return null;
                Span<byte> code = bytes[..length];
                raw.CopyTo(code);
                var decoder = Decoder.Create(64, new ByteArrayCodeReader(code.ToArray()), decoded.IP);
                decoder.Decode(out Instruction ins);
                ConstantOffsets offsets = decoder.GetConstantOffsets(ins);

                // Where the instruction sits inside the function: jumps within the function are kept as they
                // are, and mean the same only when everything is at the same place.
                BinaryPrimitives.WriteUInt32LittleEndian(note, (uint)(decoded.IP - address));
                hash.AppendData(note[..4]);

                byte tag = 0;
                ulong identity = 0;
                if (ins.IsIPRelativeMemoryOperand)
                {
                    if (offsets.HasDisplacement) code.Slice(offsets.DisplacementOffset, offsets.DisplacementSize).Clear();
                    ulong target = ins.IPRelativeMemoryAddress;
                    ImageSection? section = image.SectionAt(target);
                    bool shared = section is not { IsWritable: true } || program.Model.ResolveUsageSlot(target) != null ||
                                  program.Defaults.Slots.ContainsKey(target);
                    if (shared)
                    {
                        // A class, a string, a constant, a function: the very same one in the method and its copy.
                        tag = 1;
                        identity = target;
                    }
                    else
                    {
                        // A variable of the function's own (its "initialized" flag, a remembered pointer): each
                        // copy has its own, used in the same places.
                        privates ??= [];
                        if (!privates.TryGetValue(target, out int ordinal)) privates[target] = ordinal = privates.Count;
                        tag = 2;
                        identity = (ulong)ordinal;
                    }
                }
                else if (offsets.HasDisplacement && offsets.DisplacementSize == 4 && ins.MemoryBase != Register.None &&
                         ins.MemoryBase != Register.RSP && ins.MemoryBase != Register.RBP)
                {
                    // "image base + offset" addresses the function's own jump table.
                    ulong displacement = ins.MemoryDisplacement64 & 0xFFFFFFFF;
                    if (displacement >= 0x10000 && displacement < imageSpan)
                    {
                        bool hasMemory = false;
                        for (int i = 0; i < ins.OpCount; i++) hasMemory |= ins.GetOpKind(i) == OpKind.Memory;
                        if (hasMemory)
                        {
                            code.Slice(offsets.DisplacementOffset, 4).Clear();
                            tag = 3;
                        }
                    }
                }

                if (ins.FlowControl is FlowControl.Call or FlowControl.UnconditionalBranch or FlowControl.ConditionalBranch &&
                    ins.Op0Kind is OpKind.NearBranch64 or OpKind.NearBranch32)
                {
                    ulong target = ins.NearBranchTarget;
                    if (!inside.Contains(target))
                    {
                        if (offsets.HasImmediate) code.Slice(offsets.ImmediateOffset, offsets.ImmediateSize).Clear();
                        callees.Add(target);
                        tag |= 4;
                    }
                }

                hash.AppendData(code);
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

    public static Result Find(ProgramAnalysis program)
    {
        var result = new Result();
        NativeImage image = program.Model.Image;
        if (image.Arch is not (CpuArch.X64 or CpuArch.Arm64)) return result;
        ModelCodeContext context = program.Context;
        ulong imageSpan = 0;
        foreach (ImageSection section in image.Sections) imageSpan = Math.Max(imageSpan, section.Va + section.Size - image.ImageBase);

        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        var bodies = new Dictionary<ulong, Body?>();
        Body? BodyOf(ulong address)
        {
            if (!bodies.TryGetValue(address, out Body? body))
                bodies[address] = body = image.Arch == CpuArch.Arm64 ? DescribeArm64(program, hash, address) : Describe(program, hash, address, imageSpan);
            return body;
        }

        var listed = new List<ulong>();
        var unlisted = new List<ulong>();
        foreach (ulong start in context.FunctionStarts)
        {
            if (!image.IsCodeAddress(start)) continue;
            if (context.IsManaged(start)) listed.Add(start);
            else if (program.Helpers.At(start) == null) unlisted.Add(start);
        }
        result.Examined = unlisted.Count;

        // The identity of a function: its class representative. Starts as the function itself (through
        // jump-only stubs); functions found equal to a listed method take that method's identity.
        var identityOf = new Dictionary<ulong, ulong>();
        ulong Identity(ulong address)
        {
            address = program.Code.ThunkTarget(address);
            return identityOf.GetValueOrDefault(address, address);
        }

        Span<byte> word = stackalloc byte[16];
        UInt128 KeyOf(Body body, Span<byte> scratch)
        {
            BinaryPrimitives.WriteUInt64LittleEndian(scratch, (ulong)body.Code);
            BinaryPrimitives.WriteUInt64LittleEndian(scratch[8..], (ulong)(body.Code >> 64));
            hash.AppendData(scratch);
            foreach (ulong callee in body.Callees)
            {
                BinaryPrimitives.WriteUInt64LittleEndian(scratch, Identity(callee));
                hash.AppendData(scratch[..8]);
            }
            return Finish(hash);
        }

        for (int round = 0; round < 6; round++)
        {
            result.Rounds = round + 1;
            // Listed methods with equal code form one class, named by its lowest address.
            var classes = new Dictionary<UInt128, List<ulong>>();
            foreach (ulong address in listed)
            {
                if (BodyOf(address) is not { } body) continue;
                UInt128 key = KeyOf(body, word);
                if (!classes.TryGetValue(key, out List<ulong>? members)) classes[key] = members = [];
                members.Add(address);
            }
            var next = new Dictionary<ulong, ulong>();
            foreach (List<ulong> members in classes.Values)
                if (members.Count > 1)
                    foreach (ulong member in members)
                        next[member] = members[0];

            var copies = new Dictionary<ulong, ulong[]>();
            foreach (ulong address in unlisted)
            {
                if (BodyOf(address) is not { } body) continue;
                if (!classes.TryGetValue(KeyOf(body, word), out List<ulong>? members)) continue;
                copies[address] = members.ToArray();
                next[address] = members[0];
            }

            bool same = next.Count == identityOf.Count;
            if (same)
                foreach (var (address, identity) in next)
                    if (!identityOf.TryGetValue(address, out ulong before) || before != identity)
                    {
                        same = false;
                        break;
                    }
            identityOf = next;
            result.Copies = copies;
            if (same) break;
        }
        return result;
    }
}
