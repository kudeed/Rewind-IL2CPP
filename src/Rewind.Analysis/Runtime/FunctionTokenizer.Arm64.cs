using Gee.External.Capstone;
using Gee.External.Capstone.Arm64;
using Rewind.Binary;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// ARM64 (Android, Quest) half of the tokenizer. The scheme is the x64 one: whatever depends on where code and
/// data were loaded is replaced by what it refers to. ARM64 builds addresses in two steps ("adrp" loads the 4 KB
/// page, the next instruction adds the offset inside it), so the page is remembered per register and the
/// reference is emitted where the full address is used.
/// </summary>
public sealed partial class FunctionTokenizer
{
    private CapstoneArm64Disassembler? _arm64;
    private Dictionary<ulong, ulong>? _functionEnds;
    private readonly Dictionary<Arm64RegisterId, int> _armRegisterIndex = [];

    private const int MaxArmFunctionBytes = 1 << 20;

    /// <summary>Why the last function that could not be tokenized could not be (for diagnostics).</summary>
    public string? LastFailure { get; private set; }

    private CapstoneArm64Disassembler Arm64
    {
        get
        {
            if (_arm64 != null) return _arm64;
            _arm64 = CapstoneDisassembler.CreateArm64Disassembler(Arm64DisassembleMode.Arm);
            _arm64.EnableInstructionDetails = true;
            _arm64.EnableSkipDataMode = true; // words it cannot decode come back as data, not as the end
            return _arm64;
        }
    }

    private List<ImageSection>? _gotSections;

    /// <summary>
    /// True for an entry of the global offset table. Position-independent code reaches a global defined in
    /// another file through it: the entry holds the global's address, and the global is loaded from there.
    /// </summary>
    private bool IsGotEntry(ulong address)
    {
        _gotSections ??= _image.Sections.Where(s => s.Name is ".got" or ".got.plt").ToList();
        foreach (ImageSection s in _gotSections)
            if (s.Contains(address))
                return true;
        return false;
    }

    /// <summary>Where the function starting at <paramref name="start"/> ends: its unwind or symbol entry, else the next function.</summary>
    private ulong FunctionEnd(ulong start)
    {
        if (_functionEnds == null)
        {
            _functionEnds = [];
            foreach (FunctionRange f in _image.FunctionTable)
                if (f.End > f.Start)
                    _functionEnds.TryAdd(f.Start, f.End);
        }
        ulong next = context.NextFunctionStart(start);
        ulong end = _functionEnds.TryGetValue(start, out ulong known) ? known : next;
        if (next > start && next < end) end = next; // a listed function that starts inside: stop there
        if (end <= start) end = start + 4;
        return Math.Min(end, start + MaxArmFunctionBytes);
    }

    /// <summary>Register class * 32 + number; classes x, w, b, h, s, d, q, v, then special registers.</summary>
    private int ArmRegister(Arm64Register? register)
    {
        if (register == null) return 8 * 32 + 31;
        if (_armRegisterIndex.TryGetValue(register.Id, out int known)) return known;
        string name = register.Name ?? "";
        int index;
        switch (name)
        {
            case "sp": index = 8 * 32 + 0; break;
            case "wsp": index = 8 * 32 + 1; break;
            case "xzr": index = 8 * 32 + 2; break;
            case "wzr": index = 8 * 32 + 3; break;
            case "nzcv": index = 8 * 32 + 4; break;
            case "fp": index = 29; break;
            case "lr": index = 30; break;
            default:
            {
                int cls = name.Length > 1 ? name[0] switch { 'x' => 0, 'w' => 1, 'b' => 2, 'h' => 3, 's' => 4, 'd' => 5, 'q' => 6, 'v' => 7, _ => -1 } : -1;
                index = cls >= 0 && int.TryParse(name.AsSpan(1), out int number) && number is >= 0 and < 32 ? cls * 32 + number : 8 * 32 + 31;
                break;
            }
        }
        _armRegisterIndex[register.Id] = index;
        return index;
    }

    private static bool IsBranchWithTarget(Arm64InstructionId id) => id is Arm64InstructionId.ARM64_INS_B or Arm64InstructionId.ARM64_INS_BL
        or Arm64InstructionId.ARM64_INS_CBZ or Arm64InstructionId.ARM64_INS_CBNZ or Arm64InstructionId.ARM64_INS_TBZ or Arm64InstructionId.ARM64_INS_TBNZ;

    /// <summary>Instructions whose first register operand is read, not written.</summary>
    private static bool WritesNoRegister(string mnemonic) =>
        mnemonic.StartsWith("st", StringComparison.Ordinal) || mnemonic.StartsWith("cmp", StringComparison.Ordinal) ||
        mnemonic.StartsWith("cmn", StringComparison.Ordinal) || mnemonic.StartsWith("tst", StringComparison.Ordinal) ||
        mnemonic.StartsWith("ccm", StringComparison.Ordinal) || mnemonic.StartsWith("fcmp", StringComparison.Ordinal) ||
        mnemonic.StartsWith("fccmp", StringComparison.Ordinal) || mnemonic.StartsWith("b", StringComparison.Ordinal) ||
        mnemonic.StartsWith("cb", StringComparison.Ordinal) || mnemonic.StartsWith("tb", StringComparison.Ordinal) ||
        mnemonic is "ret" or "prfm" or "prfum" or "msr" or "dmb" or "dsb" or "isb" or "nop" or "hint" or "brk" or "udf";

    /// <summary>Bytes moved by a load or store, from its mnemonic and first register.</summary>
    private static int AccessSize(string mnemonic, Arm64Operand[] operands)
    {
        if (mnemonic.EndsWith('b') && (mnemonic.StartsWith("ld", StringComparison.Ordinal) || mnemonic.StartsWith("st", StringComparison.Ordinal))) return 1;
        if (mnemonic.EndsWith('h') && (mnemonic.StartsWith("ld", StringComparison.Ordinal) || mnemonic.StartsWith("st", StringComparison.Ordinal))) return 2;
        if (mnemonic.EndsWith("sw", StringComparison.Ordinal)) return 4;
        if (operands.Length == 0 || operands[0].Type != Arm64OperandType.Register) return 0;
        string name = operands[0].Register?.Name ?? "";
        int one = name.Length == 0 ? 0 : name[0] switch { 'x' => 8, 'w' => 4, 'q' => 16, 'd' => 8, 's' => 4, 'h' => 2, 'b' => 1, 'v' => 16, _ => 8 };
        if (name is "xzr") one = 8;
        if (name is "wzr") one = 4;
        bool pair = mnemonic.StartsWith("ldp", StringComparison.Ordinal) || mnemonic.StartsWith("stp", StringComparison.Ordinal) ||
                    mnemonic.StartsWith("ldnp", StringComparison.Ordinal) || mnemonic.StartsWith("stnp", StringComparison.Ordinal);
        return pair ? one * 2 : one;
    }

    private static int SizeClass(int size) => size switch { 1 => 0, 2 => 1, 4 => 2, 8 => 3, 16 => 4, 32 => 5, 0 => 6, _ => 7 };

    private void ArmModifiers(Arm64Operand operand, List<ushort> output)
    {
        if (operand.ShiftOperation != Arm64ShiftOperation.Invalid && operand.ShiftValue != 0)
            output.Add((ushort)(TokenVocabulary.ArmShiftBase + Math.Min(5, (int)operand.ShiftOperation) * 64 + Math.Clamp(operand.ShiftValue, 0, 63)));
        if (operand.ExtendOperation != Arm64ExtendOperation.Invalid)
            output.Add((ushort)(TokenVocabulary.ArmExtendBase + Math.Min(8, (int)operand.ExtendOperation) * 8 +
                                Math.Clamp(operand.ShiftOperation == Arm64ShiftOperation.Invalid ? 0 : operand.ShiftValue, 0, 7)));
    }

    private ushort[]? TokenizeArm64(ulong start, out int instructions)
    {
        instructions = 0;
        ulong end = FunctionEnd(start);
        int length = (int)(end - start) & ~3;
        if (length <= 0 || !_image.TrySpan(start, length, out ReadOnlySpan<byte> code))
        {
            LastFailure = $"bytes 0x{start:X}..0x{end:X} not mapped";
            return null;
        }
        Arm64Instruction[] decoded;
        try
        {
            decoded = Arm64.Disassemble(code.ToArray(), (long)start);
        }
        catch (Exception e)
        {
            LastFailure = $"disassembler: {e.GetType().Name}: {e.Message}";
            return null;
        }
        if (decoded.Length == 0)
        {
            LastFailure = $"no instructions in {length} bytes";
            return null;
        }

        var output = new List<ushort>(256) { TokenVocabulary.ArchArm64 };
        // Registers known to hold an address built with adrp (the page, or page + offset after an add).
        var addresses = new Dictionary<int, ulong>();
        foreach (Arm64Instruction ins in decoded)
        {
            instructions++;
            if (output.Count >= MaxTokens - 8) continue; // keep counting instructions, stop emitting
            if (ins.IsSkippedData || !ins.HasDetails || ins.Details == null)
            {
                output.Add(TokenVocabulary.Unknown);
                continue;
            }
            Arm64Operand[] ops = ins.Details.Operands ?? [];
            string mnemonic = ins.Mnemonic ?? "";
            Arm64InstructionId id = ins.Id;
            output.Add((ushort)(TokenVocabulary.ArmMnemonicBase + Math.Clamp((int)id, 0, TokenVocabulary.ArmMnemonicCount - 1)));
            if (ins.Details.ConditionCode != Arm64ConditionCode.Invalid)
                output.Add((ushort)(TokenVocabulary.ArmConditionBase + Math.Clamp((int)ins.Details.ConditionCode, 0, TokenVocabulary.ArmConditionCount - 1)));

            int accessSize = -1;
            ulong? gotValue = null;
            int written = !WritesNoRegister(mnemonic) && ops.Length > 0 && ops[0].Type == Arm64OperandType.Register ? ArmRegister(ops[0].Register) : -1;
            ulong? newAddress = null;

            if (id == Arm64InstructionId.ARM64_INS_ADRP && ops.Length == 2 && ops[1].Type == Arm64OperandType.Immediate)
            {
                output.Add((ushort)(TokenVocabulary.ArmRegisterBase + ArmRegister(ops[0].Register)));
                output.Add(TokenVocabulary.ArmPage);
                newAddress = (ulong)ops[1].Immediate;
            }
            else if (id == Arm64InstructionId.ARM64_INS_ADR && ops.Length == 2 && ops[1].Type == Arm64OperandType.Immediate)
            {
                output.Add((ushort)(TokenVocabulary.ArmRegisterBase + ArmRegister(ops[0].Register)));
                newAddress = (ulong)ops[1].Immediate;
                Reference(newAddress.Value, 0, output);
            }
            else if (id == Arm64InstructionId.ARM64_INS_ADD && ops.Length == 3 && ops[1].Type == Arm64OperandType.Register &&
                     ops[2].Type == Arm64OperandType.Immediate && ops[2].ShiftOperation == Arm64ShiftOperation.Invalid &&
                     addresses.TryGetValue(ArmRegister(ops[1].Register), out ulong page))
            {
                // add xd, xn, #:lo12:symbol  completes an address.
                output.Add((ushort)(TokenVocabulary.ArmRegisterBase + ArmRegister(ops[0].Register)));
                newAddress = page + (ulong)ops[2].Immediate;
                Reference(newAddress.Value, 0, output);
            }
            else
            {
                for (int i = 0; i < ops.Length; i++)
                {
                    Arm64Operand op = ops[i];
                    int before = output.Count;
                    try
                    {
                        OneOperand(op, i);
                    }
                    catch (InvalidOperationException)
                    {
                        output.RemoveRange(before, output.Count - before);
                        output.Add(TokenVocabulary.Unknown);
                    }
                }
            }

            void OneOperand(Arm64Operand op, int i)
            {
                {
                    switch (op.Type)
                    {
                        case Arm64OperandType.Register:
                            output.Add((ushort)(TokenVocabulary.ArmRegisterBase + ArmRegister(op.Register)));
                            if (op.VectorArrangementSpecifier != Arm64VectorArrangementSpecifier.Invalid)
                                output.Add((ushort)(TokenVocabulary.ArmArrangementBase + Math.Min(15, (int)op.VectorArrangementSpecifier)));
                            if (op.VectorIndex >= 0) ImmediateValue(op.VectorIndex, output);
                            ArmModifiers(op, output);
                            break;
                        case Arm64OperandType.Memory:
                        {
                            if (accessSize < 0) accessSize = AccessSize(mnemonic, ops);
                            Arm64MemoryOperandValue memory = op.Memory;
                            int baseIndex = memory?.Base == null ? -1 : ArmRegister(memory.Base);
                            bool hasIndex = memory?.Index != null && memory.Index.Id != 0;
                            bool post = ins.Details.WriteBack && i + 1 < ops.Length && ops[i + 1].Type == Arm64OperandType.Immediate;
                            int writeback = !ins.Details.WriteBack ? 0 : post ? 2 : 1;
                            int baseClass = baseIndex < 0 ? 0 : baseIndex == 8 * 32 + 0 ? 1 : baseIndex == 29 ? 2 : 3;
                            output.Add((ushort)(TokenVocabulary.ArmMemoryBase + ((SizeClass(accessSize) * 4 + baseClass) * 2 + (hasIndex ? 1 : 0)) * 3 + writeback));
                            long displacement = memory?.Displacement ?? 0;
                            if (!hasIndex && baseIndex >= 0 && addresses.TryGetValue(baseIndex, out ulong basePage))
                            {
                                ulong target = basePage + (ulong)displacement;
                                if (IsGotEntry(target) && accessSize == 8 && _image.TryPtr(target, out ulong global) && global != 0)
                                {
                                    // ldr xd, [xn, #:got_lo12:symbol]: xd now holds the address of the global - the
                                    // equivalent of x64's "lea reg, [rip + global]".
                                    Reference(global, 0, output);
                                    gotValue = global;
                                }
                                // ldr xd, [xn, #:lo12:symbol]: a load from a known address, like x64's rip-relative.
                                else Reference(target, accessSize, output);
                            }
                            else
                            {
                                if (hasIndex) output.Add((ushort)(TokenVocabulary.ArmRegisterBase + ArmRegister(memory!.Index)));
                                output.Add((ushort)(TokenVocabulary.DisplacementBase + DisplacementToken(displacement, baseClass is 1 or 2)));
                            }
                            ArmModifiers(op, output);
                            break;
                        }
                        case Arm64OperandType.Immediate or Arm64OperandType.CImmediate:
                        {
                            if (IsBranchWithTarget(id) && i == ops.Length - 1)
                            {
                                ulong target = (ulong)op.Immediate;
                                if (target >= start && target < end)
                                {
                                    bool back = target <= (ulong)ins.Address;
                                    ulong distance = back ? (ulong)ins.Address - target : target - (ulong)ins.Address;
                                    output.Add((ushort)(TokenVocabulary.BranchBase + (back ? 16 : 0) + Math.Min(15, Log2(distance + 1))));
                                }
                                else
                                {
                                    int bucket = CallBucket(target);
                                    output.Add((ushort)(bucket >= 0 ? TokenVocabulary.CallManagedBase + bucket : TokenVocabulary.CallUnlisted));
                                }
                            }
                            else if (mnemonic.StartsWith("ldr", StringComparison.Ordinal) && i == ops.Length - 1 && op.Type == Arm64OperandType.Immediate &&
                                     ops.Length == 2 && _image.SectionAt((ulong)op.Immediate) != null)
                            {
                                // ldr xd, =literal: a pc-relative load.
                                Reference((ulong)op.Immediate, AccessSize(mnemonic, ops), output);
                            }
                            else
                            {
                                ImmediateValue(op.Immediate, output);
                                ArmModifiers(op, output);
                            }
                            break;
                        }
                        case Arm64OperandType.FloatingPoint:
                            ImmediateValue(BitConverter.DoubleToInt64Bits(op.FloatingPoint), output);
                            break;
                        default:
                            output.Add(TokenVocabulary.ArmOther);
                            break;
                    }
                }
            }

            // Keep the address registers up to date.
            if (id is Arm64InstructionId.ARM64_INS_BL or Arm64InstructionId.ARM64_INS_BLR)
            {
                // A call leaves x0-x18 with nothing the caller put there.
                foreach (int r in addresses.Keys.Where(r => r < 19 || (r >= 32 && r < 32 + 19)).ToList()) addresses.Remove(r);
            }
            else if (written >= 0)
            {
                addresses.Remove(written);
                if (written < 32) addresses.Remove(written + 32); // writing wN also changes xN
                if (written is >= 32 and < 64) addresses.Remove(written - 32);
                if ((mnemonic.StartsWith("ldp", StringComparison.Ordinal) || mnemonic.StartsWith("ldnp", StringComparison.Ordinal)) &&
                    ops.Length > 1 && ops[1].Type == Arm64OperandType.Register)
                    addresses.Remove(ArmRegister(ops[1].Register));
                if (newAddress.HasValue && written < 32) addresses[written] = newAddress.Value;
                else if (gotValue.HasValue && written < 32) addresses[written] = gotValue.Value;
            }
        }
        output.Add((ushort)(output.Count >= MaxTokens - 8 ? TokenVocabulary.Truncated : TokenVocabulary.End));
        return output.ToArray();
    }
}
