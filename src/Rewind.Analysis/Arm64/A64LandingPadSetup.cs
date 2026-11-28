namespace Rewind.Analysis.Arm64;

// Equivalent terminal register values of a linear, effect-free landing prefix.
// Incoming exception/selector and the frame SP are the only allowed dependencies.
// Calls, writes, flags, indexed/writeback loads and unknown code fail closed.
internal static class A64LandingPadSetup
{
    private readonly record struct Value(string Text, ulong Dependencies);
    internal static bool EquivalentRegister(IReadOnlyList<A64Instruction> left, IReadOnlyList<A64Instruction> right, int register)
    {
        if (register is < 0 or > 30 || !Evaluate(left, out var a) || !Evaluate(right, out var b) ||
            !a.TryGetValue((byte)register, out var x) || !b.TryGetValue((byte)register, out var y)) return false;
        ulong permitted = (1UL << 0) | (1UL << 1) | (1UL << A64Instruction.Sp);
        return x == y && (x.Dependencies & ~permitted) == 0;
    }
    private static bool Evaluate(IReadOnlyList<A64Instruction> instructions, out Dictionary<byte, Value> values)
    {
        values = [];
        if (instructions.Count is 0 or > 64) return false;
        // Do not capture an out parameter in local functions.
        var state = values;
        Value Read(byte reg) => reg == A64Instruction.Zr ? new Value("c:0", 0) :
            state.TryGetValue(reg, out var value) ? value : new Value("r:" + reg, 1UL << reg);
        Value Width(Value value, bool wide) => wide ? value : value with { Text = "u32(" + value.Text + ")" };
        foreach (var i in instructions)
        {
            if (i.SetFlags || i.IsInvalid || i.Vector) return false;
            Value value;
            switch (i.Op)
            {
                case A64Op.Nop: continue;
                case A64Op.Adr or A64Op.Adrp when i.Is64:
                    value = new Value("c:" + i.Target, 0); break;
                case A64Op.Orr when i.Rn == A64Instruction.Zr && i.Amount == 0 && i.Shift == A64Shift.Lsl:
                    value = Width(Read(i.Rm), i.Is64); break;
                case A64Op.AddImm:
                    var source = Read(i.Rn);
                    value = Width(i.Imm == 0 ? source : source with { Text = "add(" + source.Text + "," + i.Imm + ")" }, i.Is64); break;
                case A64Op.Ldr when i.Mode == A64Mode.Offset && i.Size is 1 or 2 or 4 or 8:
                    var address = Read(i.Rn);
                    value = new Value($"load({i.Size},{i.Is64},{i.Signed},{address.Text},{i.Imm})", address.Dependencies); break;
                default: return false;
            }
            if (i.Rd == A64Instruction.Sp) return false;
            if (i.Rd != A64Instruction.Zr) state[i.Rd] = value;
        }
        return true;
    }
}
