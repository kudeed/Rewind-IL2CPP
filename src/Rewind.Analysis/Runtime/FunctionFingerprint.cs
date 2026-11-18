using System.Security.Cryptography;
using System.Text;
using Iced.Intel;
using Decoder = Iced.Intel.Decoder;
using Rewind.Analysis.X64;
using Rewind.Binary;

namespace Rewind.Analysis.Runtime;

/// <summary>Identity of a function's machine code that does not depend on where the function or its callees are loaded.</summary>
public readonly record struct Fingerprint(int Length, ulong Hash)
{
    public override string ToString() => $"{Length:X}:{Hash:X16}";

    public static Fingerprint Parse(string text)
    {
        int colon = text.IndexOf(':');
        return new Fingerprint(Convert.ToInt32(text[..colon], 16), Convert.ToUInt64(text[(colon + 1)..], 16));
    }
}

/// <summary>What one native function consists of, with everything position-dependent removed.</summary>
public sealed class FunctionCode
{
    /// <summary>Hash of the instruction bytes with distances to other code and data blanked.</summary>
    public Fingerprint Shallow;
    /// <summary>Direct call and tail-jump targets outside the function, in address order of the instructions.</summary>
    public List<ulong> Callees = [];
    /// <summary>Text the function refers to: string constants and the names of imported functions it calls.</summary>
    public List<string> Names = [];
    /// <summary>Number of instructions.</summary>
    public int Instructions;
    /// <summary>
    /// A similarity sketch: the smallest hashes of all runs of three consecutive instructions, each reduced to
    /// its operation and operand shapes. Functions that differ in a few places share most of their sketch.
    /// </summary>
    public uint[] Sketch = [];
    /// <summary>True when the function is nothing but a jump to another function.</summary>
    public bool IsThunk => Instructions == 1 && Callees.Count == 1;
}

/// <summary>
/// Position-independent fingerprints of native functions.
///
/// Two builds made with the same compiler from the same runtime sources contain byte-identical support
/// functions, except for the fields that encode distances to other code and data. Those fields are blanked
/// before hashing (the "shallow" fingerprint). Many small functions are then indistinguishable - every
/// "call something; trap" wrapper looks alike - so the "deep" fingerprint also folds in the fingerprints of the
/// functions called, recursively, and the string constants referenced along the way. That tells
/// "raise NullReferenceException" from "raise IndexOutOfRangeException" although their own bytes are equal.
/// </summary>
public sealed partial class CodeIndex(ICodeContext context)
{
    private readonly NativeImage _image = context.Image;
    private readonly Dictionary<ulong, FunctionCode?> _code = [];
    private readonly Dictionary<(ulong, int), Fingerprint> _deep = [];
    private ulong _imageEnd;

    public const int DefaultDepth = 4;

    private ulong ImageEnd
    {
        get
        {
            if (_imageEnd != 0) return _imageEnd;
            ulong end = _image.ImageBase;
            foreach (ImageSection section in _image.Sections) end = Math.Max(end, section.Va + section.Size);
            return _imageEnd = end;
        }
    }

    private string? StringAt(ulong va)
    {
        ImageSection? section = _image.SectionAt(va);
        if (section == null || section.IsExecutable) return null;
        string? text = _image.TryCString(va, 96);
        if (text == null || text.Length < 3) return null;
        foreach (char c in text)
            if (c < 0x20 || c > 0x7E)
                return null;
        return text;
    }

    public FunctionCode? Get(ulong address)
    {
        if (_code.TryGetValue(address, out FunctionCode? cached)) return cached;
        FunctionCode? result = Compute(address);
        _code[address] = result;
        return result;
    }

    private FunctionCode? Compute(ulong address)
    {
        if (_image.Arch == CpuArch.Arm64) return ComputeArm64(address);
        X64Cfg cfg = X64Cfg.Build(context, address);
        if (cfg.Blocks.Count == 0) return null;
        var inside = new HashSet<ulong>();
        foreach (RawBlock block in cfg.Blocks)
            foreach (Instruction ins in block.Instructions)
                inside.Add(ins.IP);

        var result = new FunctionCode();
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        int total = 0;
        var tokens = new List<uint>();
        var decoder = Decoder.Create(64, new ByteArrayCodeReader([]), 0);
        Span<byte> scratch = stackalloc byte[16];

        foreach (RawBlock block in cfg.Blocks.OrderBy(b => b.Start))
        {
            foreach (Instruction decoded in block.Instructions)
            {
                if (decoded.IsInvalid) return null;
                int length = decoded.Length;
                if (!_image.TrySpan(decoded.IP, length, out ReadOnlySpan<byte> raw)) return null;
                Span<byte> bytes = scratch[..length];
                raw.CopyTo(bytes);

                // Decode again to learn where the displacement and immediate fields sit.
                decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes.ToArray()), decoded.IP);
                decoder.Decode(out Instruction ins);
                ConstantOffsets offsets = decoder.GetConstantOffsets(ins);

                bool hasMemory = false;
                for (int i = 0; i < ins.OpCount; i++)
                    if (ins.GetOpKind(i) == OpKind.Memory)
                        hasMemory = true;

                if (ins.IsIPRelativeMemoryOperand)
                {
                    if (offsets.HasDisplacement) bytes.Slice(offsets.DisplacementOffset, offsets.DisplacementSize).Clear();
                    ulong target = ins.IPRelativeMemoryAddress;
                    if (ins.FlowControl is FlowControl.IndirectCall or FlowControl.IndirectBranch && _image.ImportSlots.TryGetValue(target, out string? import))
                        result.Names.Add("import:" + import);
                    else if (ins.Mnemonic == Mnemonic.Lea && StringAt(target) is { } text)
                        result.Names.Add(text);
                }
                else if (hasMemory && offsets.HasDisplacement && offsets.DisplacementSize == 4 && ins.MemoryBase != Register.None &&
                         ins.MemoryBase != Register.RSP && ins.MemoryBase != Register.RBP)
                {
                    // Jump and lookup tables are addressed as "image base + offset": the offset moves with the image.
                    ulong displacement = ins.MemoryDisplacement64 & 0xFFFFFFFF;
                    if (displacement >= 0x10000 && displacement < ImageEnd - _image.ImageBase)
                        bytes.Slice(offsets.DisplacementOffset, 4).Clear();
                }

                if (ins.FlowControl is FlowControl.Call or FlowControl.UnconditionalBranch or FlowControl.ConditionalBranch &&
                    ins.Op0Kind is OpKind.NearBranch64 or OpKind.NearBranch32)
                {
                    ulong target = ins.NearBranchTarget;
                    if (!inside.Contains(target))
                    {
                        if (offsets.HasImmediate) bytes.Slice(offsets.ImmediateOffset, offsets.ImmediateSize).Clear();
                        if (ins.FlowControl != FlowControl.ConditionalBranch) result.Callees.Add(target);
                    }
                }

                // A 64-bit immediate that is an address inside the image moves with the image.
                if (offsets.HasImmediate && offsets.ImmediateSize == 8)
                {
                    ulong imm = ins.GetImmediate(ins.OpCount - 1);
                    if (imm >= _image.ImageBase && imm < ImageEnd) bytes.Slice(offsets.ImmediateOffset, 8).Clear();
                }

                hash.AppendData(bytes);
                total += length;
                tokens.Add(Token(ins));
            }
        }
        result.Shallow = new Fingerprint(total, BitConverter.ToUInt64(hash.GetHashAndReset()));
        result.Instructions = tokens.Count;
        result.Sketch = MakeSketch(tokens);
        return result;
    }

    public const int SketchSize = 64;

    private static uint Mix(uint h, uint value)
    {
        h ^= value;
        h *= 0x9E3779B1;
        return h ^ (h >> 15);
    }

    /// <summary>What an instruction does, without the registers and addresses that vary between builds.</summary>
    private static uint Token(in Instruction ins)
    {
        uint h = Mix(0x811C9DC5, (uint)ins.Mnemonic);
        for (int i = 0; i < ins.OpCount; i++)
        {
            OpKind kind = ins.GetOpKind(i);
            switch (kind)
            {
                case OpKind.Register:
                    h = Mix(h, 1u + (uint)ins.GetOpRegister(i).GetSize());
                    break;
                case OpKind.Memory:
                    h = Mix(h, 100u + (uint)ins.MemorySize);
                    if (!ins.IsIPRelativeMemoryOperand && ins.MemoryDisplacement64 < 0x800) h = Mix(h, (uint)ins.MemoryDisplacement64);
                    break;
                case OpKind.NearBranch64 or OpKind.NearBranch32 or OpKind.NearBranch16:
                    h = Mix(h, 200u);
                    break;
                case OpKind.Immediate8 or OpKind.Immediate8_2nd or OpKind.Immediate16 or OpKind.Immediate32 or OpKind.Immediate64
                    or OpKind.Immediate8to16 or OpKind.Immediate8to32 or OpKind.Immediate8to64 or OpKind.Immediate32to64:
                {
                    ulong imm = ins.GetImmediate(i);
                    h = Mix(h, 300u);
                    if (imm < 0x10000) h = Mix(h, (uint)imm);
                    break;
                }
                default:
                    h = Mix(h, 400u + (uint)kind);
                    break;
            }
        }
        return h;
    }

    private static uint[] MakeSketch(List<uint> tokens)
    {
        var smallest = new SortedSet<uint>();
        int n = tokens.Count;
        int width = Math.Min(3, n);
        for (int i = 0; i + width <= n; i++)
        {
            uint h = 0x1234567;
            for (int k = 0; k < width; k++) h = Mix(h, tokens[i + k]);
            if (smallest.Count < SketchSize) smallest.Add(h);
            else if (h < smallest.Max && smallest.Add(h)) smallest.Remove(smallest.Max);
        }
        return smallest.ToArray();
    }

    /// <summary>Estimated share of instruction runs two functions have in common (0..1).</summary>
    public static double Similarity(uint[] a, uint[] b)
    {
        if (a.Length == 0 || b.Length == 0) return 0;
        int i = 0, j = 0, taken = 0, common = 0;
        int limit = Math.Min(SketchSize, Math.Max(a.Length, b.Length));
        while (taken < limit && (i < a.Length || j < b.Length))
        {
            if (j >= b.Length || (i < a.Length && a[i] < b[j])) i++;
            else if (i >= a.Length || b[j] < a[i]) j++;
            else
            {
                common++;
                i++;
                j++;
            }
            taken++;
        }
        return taken == 0 ? 0 : (double)common / taken;
    }

    /// <summary>The function a chain of jump-only functions ends in.</summary>
    public ulong ThunkTarget(ulong address)
    {
        for (int hops = 0; hops < 8; hops++)
        {
            FunctionCode? code = Get(address);
            if (code == null || !code.IsThunk) break;
            address = code.Callees[0];
        }
        return address;
    }

    /// <summary>Fingerprint of a function together with what it calls and names, to the given depth.</summary>
    public Fingerprint? Deep(ulong address, int depth = DefaultDepth)
    {
        if (_deep.TryGetValue((address, depth), out Fingerprint known)) return known;
        FunctionCode? code = Get(address);
        if (code == null) return null;

        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        hash.AppendData(BitConverter.GetBytes(code.Shallow.Hash));
        hash.AppendData(BitConverter.GetBytes(code.Shallow.Length));
        foreach (string name in code.Names)
        {
            hash.AppendData(Encoding.ASCII.GetBytes(name));
            hash.AppendData([0]);
        }
        if (depth > 0)
        {
            foreach (ulong callee in code.Callees)
            {
                Fingerprint inner = Deep(callee, depth - 1) ?? default;
                hash.AppendData(BitConverter.GetBytes(inner.Hash));
                hash.AppendData(BitConverter.GetBytes(inner.Length));
            }
        }
        var result = new Fingerprint(code.Shallow.Length, BitConverter.ToUInt64(hash.GetHashAndReset()));
        _deep[(address, depth)] = result;
        return result;
    }

    /// <summary>
    /// The fingerprint the function would have, one level deep, if what it calls had the given fingerprints (one
    /// for each call, in order): Deep(address, 1) with other functions in place of its callees.
    /// </summary>
    public Fingerprint? WithCallees(ulong address, IReadOnlyList<Fingerprint> callees)
    {
        FunctionCode? code = Get(address);
        if (code == null || callees.Count != code.Callees.Count) return null;
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        hash.AppendData(BitConverter.GetBytes(code.Shallow.Hash));
        hash.AppendData(BitConverter.GetBytes(code.Shallow.Length));
        foreach (string name in code.Names)
        {
            hash.AppendData(Encoding.ASCII.GetBytes(name));
            hash.AppendData([0]);
        }
        foreach (Fingerprint inner in callees)
        {
            hash.AppendData(BitConverter.GetBytes(inner.Hash));
            hash.AppendData(BitConverter.GetBytes(inner.Length));
        }
        return new Fingerprint(code.Shallow.Length, BitConverter.ToUInt64(hash.GetHashAndReset()));
    }
}
