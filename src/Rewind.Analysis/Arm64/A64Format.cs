using System.Text;

namespace Rewind.Analysis.Arm64;

/// <summary>A readable rendering of decoded instructions, for problems and lab output (not assembler syntax).</summary>
public static class A64Format
{
    private static readonly string[] Conditions = ["eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"];

    public static string Condition(int cond) => Conditions[cond & 15];

    public static string Gpr(byte r, bool is64) => r switch
    {
        A64Instruction.Sp => is64 ? "sp" : "wsp",
        A64Instruction.Zr => is64 ? "xzr" : "wzr",
        _ => (is64 ? "x" : "w") + r,
    };

    public static string Describe(in A64Instruction i)
    {
        var sb = new StringBuilder();
        sb.Append(i.Op.ToString().ToLowerInvariant());
        if (i.SetFlags) sb.Append("(s)");
        if (i.Op == A64Op.BCond) sb.Append('.').Append(Condition(i.Cond));
        bool memory = i.Op is A64Op.Ldr or A64Op.Str or A64Op.Ldp or A64Op.Stp;
        if (memory)
        {
            string reg = i.Vector ? "v" + i.Rd : Gpr(i.Rd, i.Is64);
            sb.Append(' ').Append(reg);
            if (i.Op is A64Op.Ldp or A64Op.Stp) sb.Append(", ").Append(i.Vector ? "v" + i.Ra : Gpr(i.Ra, i.Is64));
            sb.Append($" [{Gpr(i.Rn, true)}");
            if (i.Mode == A64Mode.RegOffset) sb.Append($", {Gpr(i.Rm, true)} {i.Extend} #{i.Amount}");
            else if (i.Mode == A64Mode.Offset && i.Imm != 0) sb.Append($", #{i.Imm}");
            sb.Append(']');
            if (i.Mode == A64Mode.PreIndex) sb.Append($"! #{i.Imm}");
            if (i.Mode == A64Mode.PostIndex) sb.Append($", #{i.Imm}");
            sb.Append($" size {i.Size}");
            if (i.Signed) sb.Append(" signed");
            return sb.ToString();
        }
        sb.Append($" d={i.Rd} n={i.Rn} m={i.Rm}");
        if (i.Ra != 0) sb.Append($" a={i.Ra}");
        if (i.Imm != 0) sb.Append($" #0x{i.Imm:X}");
        if (i.Imm2 != 0) sb.Append($" #0x{i.Imm2:X}");
        if (i.Amount != 0) sb.Append($" {i.Shift}/{i.Extend} #{i.Amount}");
        if (i.Op is A64Op.Csel or A64Op.Csinc or A64Op.Csinv or A64Op.Csneg or A64Op.FCsel or A64Op.CcmpImm or A64Op.CcmpReg
            or A64Op.CcmnImm or A64Op.CcmnReg or A64Op.FCcmp or A64Op.FCcmpe) sb.Append(' ').Append(Condition(i.Cond));
        if (i.Target != 0) sb.Append($" -> 0x{i.Target:X}");
        if (i.FpSize != 0) sb.Append($" fp{i.FpSize * 8}");
        if (!i.Is64 && i.FpSize == 0 && !i.Vector) sb.Append(" (32-bit)");
        return sb.ToString();
    }
}
