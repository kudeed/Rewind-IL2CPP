using System.Text;
using Iced.Intel;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// The fixed vocabulary in which a function's machine code is shown to the identification model. Ids are
/// computed, not learned from data, so every build - and the C# tool at inference time - produces the same
/// tokens for the same code.
/// </summary>
public static class TokenVocabulary
{
    public const int Pad = 0, Cls = 1, Mask = 2, End = 3, Unknown = 4, Truncated = 5;
    /// <summary>First token of every function: which instruction set the rest is in.</summary>
    public const int ArchX64 = 6, ArchArm64 = 7;

    public const int MnemonicBase = 16, MnemonicCount = 2048;
    public const int RegisterBase = MnemonicBase + MnemonicCount, RegisterCount = 256;
    public const int MemoryBase = RegisterBase + RegisterCount, MemoryCount = 8 * 19 * 2 * 4;
    public const int DisplacementBase = MemoryBase + MemoryCount, DisplacementCount = 1024 + 256 + 64 + 32;
    public const int ImmediateBase = DisplacementBase + DisplacementCount, ImmediateCount = 1152 + 128;
    public const int ValueHashBase = ImmediateBase + ImmediateCount, ValueHashCount = 1024;
    public const int BranchBase = ValueHashBase + ValueHashCount, BranchCount = 32;
    public const int CallManagedBase = BranchBase + BranchCount, CallManagedCount = 4096;
    public const int CallUnlisted = CallManagedBase + CallManagedCount;
    public const int ReferenceKindBase = CallUnlisted + 1, ReferenceKindCount = 16;
    public const int ReferenceNameBase = ReferenceKindBase + ReferenceKindCount, ReferenceNameCount = 4096;

    // ARM64. Displacements, immediates, branches, calls and references use the shared blocks above, so the
    // same field offset, constant, callee or metadata reference is the same token in either instruction set.
    public const int ArmMnemonicBase = ReferenceNameBase + ReferenceNameCount, ArmMnemonicCount = 512;
    public const int ArmRegisterBase = ArmMnemonicBase + ArmMnemonicCount, ArmRegisterCount = 9 * 32;
    public const int ArmShiftBase = ArmRegisterBase + ArmRegisterCount, ArmShiftCount = 6 * 64;
    public const int ArmExtendBase = ArmShiftBase + ArmShiftCount, ArmExtendCount = 9 * 8;
    public const int ArmConditionBase = ArmExtendBase + ArmExtendCount, ArmConditionCount = 32;
    public const int ArmArrangementBase = ArmConditionBase + ArmConditionCount, ArmArrangementCount = 16;
    public const int ArmMemoryBase = ArmArrangementBase + ArmArrangementCount, ArmMemoryCount = 8 * 4 * 2 * 3;
    /// <summary>"The address of a 4 KB page" (adrp): what it points to is shown where it is used.</summary>
    public const int ArmPage = ArmMemoryBase + ArmMemoryCount;
    /// <summary>System register, barrier, prefetch and other operands with no data meaning.</summary>
    public const int ArmOther = ArmPage + 1;
    public const int Size = ArmOther + 1;

    /// <summary>A hash that is the same in every build and every runtime (string.GetHashCode is neither).</summary>
    public static uint StableHash(string text)
    {
        uint h = 2166136261;
        foreach (byte b in Encoding.UTF8.GetBytes(text))
        {
            h ^= b;
            h *= 16777619;
        }
        return h;
    }

    public static uint StableHash(ReadOnlySpan<byte> bytes)
    {
        uint h = 2166136261;
        foreach (byte b in bytes)
        {
            h ^= b;
            h *= 16777619;
        }
        return h;
    }
}

/// <summary>
/// Turns one function's machine code into tokens. Everything that depends on where the code was loaded is
/// replaced by what it refers to: a branch by its direction and distance, a call by the identity of the
/// method called (managed methods are named by the game's own metadata), a load from a metadata slot by the
/// kind and name of the type, method or string it denotes, a constant from read-only data by its value.
/// </summary>
public sealed partial class FunctionTokenizer(Il2CppModel model, ICodeContext context)
{
    private readonly NativeImage _image = model.Image;
    private readonly Dictionary<ulong, int> _callBucket = [];
    private ulong _imageEnd;

    public const int MaxTokens = 1024;

    /// <summary>The name a method has regardless of build and of generic instantiation.</summary>
    public static string DefinitionKey(MethodDef method) =>
        method.DeclaringType.ReflectionName + "::" + method.Name + "/" + method.Parameters.Length;

    public static string NameOf(TypeSig? type) => type switch
    {
        null => "?",
        SzArraySig a => NameOf(a.ElementType) + "[]",
        { Definition: { } definition } => definition.ReflectionName,
        _ => type.DisplayName,
    };

    private ulong ImageEnd
    {
        get
        {
            if (_imageEnd != 0) return _imageEnd;
            ulong end = _image.ImageBase;
            foreach (ImageSection s in _image.Sections) end = Math.Max(end, s.Va + s.Size);
            return _imageEnd = end;
        }
    }

    /// <summary>The bucket that stands for "a call to this managed method", or -1 when the address is not a listed method.</summary>
    private int CallBucket(ulong address)
    {
        if (_callBucket.TryGetValue(address, out int known)) return known;
        string? key = null;
        // Several methods can share one body; the smallest name is as good a representative as any and stable.
        if (model.MethodsByAddress.TryGetValue(address, out List<MethodDef>? methods))
            foreach (MethodDef m in methods)
            {
                string k = DefinitionKey(m);
                if (key == null || string.CompareOrdinal(k, key) < 0) key = k;
            }
        if (model.InstsByAddress.TryGetValue(address, out List<MethodInst>? insts))
            foreach (MethodInst inst in insts)
            {
                string k = DefinitionKey(inst.Method);
                if (key == null || string.CompareOrdinal(k, key) < 0) key = k;
            }
        int bucket = key == null ? -1 : (int)(TokenVocabulary.StableHash(key) % TokenVocabulary.CallManagedCount);
        _callBucket[address] = bucket;
        return bucket;
    }

    private static int Log2(ulong value)
    {
        int bits = 0;
        while (value > 1)
        {
            value >>= 1;
            bits++;
        }
        return bits;
    }

    private void Reference(ulong target, int operandSize, List<ushort> output)
    {
        void Kind(int kind) => output.Add((ushort)(TokenVocabulary.ReferenceKindBase + kind));
        void Name(uint hash) => output.Add((ushort)(TokenVocabulary.ReferenceNameBase + hash % TokenVocabulary.ReferenceNameCount));

        if (model.ResolveUsageSlot(target) is { } usage)
        {
            Kind((int)usage.Kind - 1);
            string name = usage.Kind switch
            {
                UsageKind.TypeInfo or UsageKind.Il2CppType => NameOf(usage.Type),
                UsageKind.MethodDef or UsageKind.MethodRef => usage.Method != null ? DefinitionKey(usage.Method) : "?",
                UsageKind.FieldInfo or UsageKind.FieldRva => usage.Field != null ? usage.Field.DeclaringType.ReflectionName + "." + usage.Field.Name : "?",
                UsageKind.StringLiteral => "\"" + (usage.String ?? ""),
                _ => "?",
            };
            Name(TokenVocabulary.StableHash(name));
            return;
        }
        if (_image.ImportSlots.TryGetValue(target, out string? import))
        {
            Kind(10);
            Name(TokenVocabulary.StableHash("import:" + import));
            return;
        }
        ImageSection? section = _image.SectionAt(target);
        if (section == null)
        {
            Kind(11);
            return;
        }
        if (section.IsExecutable)
        {
            Kind(9);
            int bucket = CallBucket(target);
            if (bucket >= 0) output.Add((ushort)(TokenVocabulary.CallManagedBase + bucket));
            return;
        }
        if (section.IsWritable)
        {
            Kind(8);
            return;
        }
        // Read-only data: a constant. Its value is what matters, and the value is the same in every build.
        string? text = operandSize == 0 ? _image.TryCString(target, 64) : null;
        if (text is { Length: >= 3 } && text.All(c => c is >= ' ' and <= '~'))
        {
            Kind(12);
            Name(TokenVocabulary.StableHash(text));
            return;
        }
        Kind(7);
        int size = operandSize is 4 or 8 or 16 ? operandSize : 8;
        if (_image.TrySpan(target, size, out ReadOnlySpan<byte> bytes)) Name(TokenVocabulary.StableHash(bytes));
    }

    /// <summary>The tokens of the function starting at <paramref name="start"/>, or null when it does not decode.</summary>
    public ushort[]? Tokenize(ulong start, out int instructions)
    {
        instructions = 0;
        if (_image.Arch == CpuArch.Arm64) return TokenizeArm64(start, out instructions);
        if (_image.Arch != CpuArch.X64) return null;
        X64Cfg cfg = X64Cfg.Build(context, start);
        if (cfg.Blocks.Count == 0) return null;
        var inside = new HashSet<ulong>();
        foreach (RawBlock block in cfg.Blocks)
            foreach (Instruction ins in block.Instructions)
                inside.Add(ins.IP);

        var output = new List<ushort>(256) { TokenVocabulary.ArchX64 };
        foreach (RawBlock block in cfg.Blocks.OrderBy(b => b.Start))
        {
            foreach (Instruction ins in block.Instructions)
            {
                if (ins.IsInvalid) return null;
                instructions++;
                if (output.Count >= MaxTokens - 8) continue; // keep counting instructions, stop emitting
                output.Add((ushort)(TokenVocabulary.MnemonicBase + Math.Min((int)ins.Mnemonic, TokenVocabulary.MnemonicCount - 1)));
                for (int i = 0; i < ins.OpCount; i++)
                {
                    switch (ins.GetOpKind(i))
                    {
                        case OpKind.Register:
                            output.Add((ushort)(TokenVocabulary.RegisterBase + Math.Min((int)ins.GetOpRegister(i), TokenVocabulary.RegisterCount - 1)));
                            break;
                        case OpKind.Memory:
                            Memory(ins, output);
                            break;
                        case OpKind.NearBranch64 or OpKind.NearBranch32 or OpKind.NearBranch16:
                        {
                            ulong target = ins.NearBranchTarget;
                            if (inside.Contains(target))
                            {
                                bool back = target <= ins.IP;
                                ulong distance = back ? ins.IP - target : target - ins.IP;
                                output.Add((ushort)(TokenVocabulary.BranchBase + (back ? 16 : 0) + Math.Min(15, Log2(distance + 1))));
                            }
                            else
                            {
                                int bucket = CallBucket(target);
                                output.Add((ushort)(bucket >= 0 ? TokenVocabulary.CallManagedBase + bucket : TokenVocabulary.CallUnlisted));
                            }
                            break;
                        }
                        case OpKind.Immediate8 or OpKind.Immediate8_2nd or OpKind.Immediate16 or OpKind.Immediate32 or OpKind.Immediate64
                            or OpKind.Immediate8to16 or OpKind.Immediate8to32 or OpKind.Immediate8to64 or OpKind.Immediate32to64:
                            Immediate(ins, i, output);
                            break;
                        default:
                            output.Add(TokenVocabulary.Unknown);
                            break;
                    }
                }
            }
        }
        output.Add((ushort)(output.Count >= MaxTokens - 8 ? TokenVocabulary.Truncated : TokenVocabulary.End));
        return output.ToArray();
    }

    /// <summary>The displacement of a memory access, as a token shared by both instruction sets.</summary>
    private static int DisplacementToken(long displacement, bool stack)
    {
        if (stack) return 1024 + 256 + 64 + (displacement < 0 ? 16 : 0) + Math.Min(15, Log2((ulong)Math.Abs(displacement) + 1));
        if (displacement is >= 0 and < 1024) return (int)displacement;
        if (displacement is < 0 and >= -256) return 1024 + (int)(-displacement - 1);
        // A large offset relative to a register is usually "image base + table": it moves with the image.
        return 1024 + 256 + (displacement < 0 ? 32 : 0) + Math.Min(31, Log2((ulong)Math.Abs(displacement)));
    }

    /// <summary>An immediate operand, as tokens shared by both instruction sets.</summary>
    private static void ImmediateValue(long value, List<ushort> output)
    {
        if (value is >= -128 and < 1024)
        {
            output.Add((ushort)(TokenVocabulary.ImmediateBase + (int)(value + 128)));
            return;
        }
        output.Add((ushort)(TokenVocabulary.ImmediateBase + 1152 + (value < 0 ? 64 : 0) + Math.Min(63, Log2(value == long.MinValue ? ulong.MaxValue : (ulong)Math.Abs(value)))));
        // Large constants are often what identifies an algorithm (hash multipliers, magic divisors, masks).
        Span<byte> bytes = stackalloc byte[8];
        BitConverter.TryWriteBytes(bytes, value);
        output.Add((ushort)(TokenVocabulary.ValueHashBase + TokenVocabulary.StableHash(bytes) % TokenVocabulary.ValueHashCount));
    }

    private void Memory(in Instruction ins, List<ushort> output)
    {
        int size = ins.MemorySize.GetSize();
        int sizeClass = size switch { 1 => 0, 2 => 1, 4 => 2, 8 => 3, 16 => 4, 32 => 5, 0 => 6, _ => 7 };
        Register baseRegister = ins.MemoryBase;
        int baseClass = baseRegister == Register.None ? 0
            : baseRegister is Register.RIP or Register.EIP ? 1
            : baseRegister.GetFullRegister() is >= Register.RAX and <= Register.R15 ? 2 + (baseRegister.GetFullRegister() - Register.RAX)
            : 18;
        int hasIndex = ins.MemoryIndex != Register.None ? 1 : 0;
        int scale = ins.MemoryIndexScale switch { 2 => 1, 4 => 2, 8 => 3, _ => 0 };
        output.Add((ushort)(TokenVocabulary.MemoryBase + ((sizeClass * 19 + baseClass) * 2 + hasIndex) * 4 + scale));

        if (ins.IsIPRelativeMemoryOperand)
        {
            Reference(ins.IPRelativeMemoryAddress, ins.Mnemonic == Mnemonic.Lea ? 0 : size, output);
            return;
        }
        long displacement = (long)ins.MemoryDisplacement64;
        if (ins.MemoryDisplSize == 0) displacement = 0;
        bool stack = baseRegister.GetFullRegister() is Register.RSP or Register.RBP;
        int token;
        if (stack) token = 1024 + 256 + 64 + (displacement < 0 ? 16 : 0) + Math.Min(15, Log2((ulong)Math.Abs(displacement) + 1));
        else if (displacement is >= 0 and < 1024) token = (int)displacement;
        else if (displacement is < 0 and >= -256) token = 1024 + (int)(-displacement - 1);
        else
        {
            // A large offset relative to a register is usually "image base + table": it moves with the image.
            token = 1024 + 256 + (displacement < 0 ? 32 : 0) + Math.Min(31, Log2((ulong)Math.Abs(displacement)));
        }
        output.Add((ushort)(TokenVocabulary.DisplacementBase + token));
    }

    private void Immediate(in Instruction ins, int operand, List<ushort> output)
    {
        ulong raw = ins.GetImmediate(operand);
        long value = ins.GetOpKind(operand) switch
        {
            OpKind.Immediate8 or OpKind.Immediate8_2nd => (sbyte)raw,
            OpKind.Immediate16 => (short)raw,
            OpKind.Immediate32 => (int)raw,
            _ => (long)raw,
        };
        if (ins.GetOpKind(operand) == OpKind.Immediate64 && raw >= _image.ImageBase && raw < ImageEnd)
        {
            Reference(raw, 0, output);
            return;
        }
        if (value is >= -128 and < 1024)
        {
            output.Add((ushort)(TokenVocabulary.ImmediateBase + (int)(value + 128)));
            return;
        }
        output.Add((ushort)(TokenVocabulary.ImmediateBase + 1152 + (value < 0 ? 64 : 0) + Math.Min(63, Log2((ulong)Math.Abs(value)))));
        // Large constants are often what identifies an algorithm (hash multipliers, magic divisors, masks).
        Span<byte> bytes = stackalloc byte[8];
        BitConverter.TryWriteBytes(bytes, value);
        output.Add((ushort)(TokenVocabulary.ValueHashBase + TokenVocabulary.StableHash(bytes) % TokenVocabulary.ValueHashCount));
    }
}
