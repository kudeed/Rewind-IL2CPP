using Rewind.Analysis.Arm64;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// The no-argument exception helpers have a small, completely linear native call chain. A recognized null
/// thrower anchors the runtime's image getter, typed factory and raiser. Another exception is accepted only
/// when its complete functions use those same targets and supply the exact System exception type name.
/// </summary>
internal static class Arm64ExceptionChain
{
    internal sealed record Contract(ulong ImageGetter, ulong Factory, ulong Raise);

    internal static Contract? FromNullThrower(ulong root, Func<ulong, A64Instruction[]> body, Func<ulong, string?> text)
    {
        var seen = new HashSet<ulong>();
        for (int depth = 0; depth < 4 && seen.Add(root); depth++)
        {
            A64Instruction[] ins = body(root);
            if (CallOnly(ins) is { } alias) { root = alias; continue; }
            // Empty StringView<Il2CppChar> on the stack, forwarded to the message-taking null thrower.
            if (ins.Length == 5 && Words(ins, (0, 0xD10083FF), (1, 0xA900FBFF), (2, 0x910003E0), (3, 0xF90003FF)) &&
                ins[4].Op == A64Op.Bl) { root = ins[4].Target; continue; }
            if (Raise(ins) is not { } raise) return null;
            A64Instruction[] factory = body(raise.Factory);
            if (factory.Length != 10 || !Words(factory, (0, 0xA9BF4FFE), (1, 0xAA0003F3), (7, 0xAA1303E3), (8, 0xA8C14FFE)) ||
                factory[2].Op != A64Op.Bl || factory[9].Op != A64Op.B ||
                Literal(factory, 3, 1, text) != "System" || Literal(factory, 5, 2, text) != "NullReferenceException") return null;
            return new Contract(factory[2].Target, factory[9].Target, raise.Raiser);
        }
        return null;
    }

    internal static bool IsIndexFactory(A64Instruction[] ins, Contract known, Func<ulong, string?> text)
    {
        // Entire function: empty message; GetCorlib(); FromNameMsg(...); restore frame; return that object.
        return ins.Length == 13 && Words(ins, (0, 0xD10083FF), (1, 0xA900FBFF), (2, 0xF90003FF),
                (8, 0x910003E3), (10, 0xF9400BFE), (11, 0x910083FF), (12, 0xD65F03C0)) &&
            ins[3].Op == A64Op.Bl && ins[3].Target == known.ImageGetter &&
            Literal(ins, 4, 1, text) == "System" && Literal(ins, 6, 2, text) == "IndexOutOfRangeException" &&
            ins[9].Op == A64Op.Bl && ins[9].Target == known.Factory;
    }

    internal static (ulong Factory, ulong Raiser)? Raise(A64Instruction[] ins) =>
        ins.Length == 4 && Words(ins, (0, 0xF81F0FFE), (2, 0xAA1F03E1)) && ins[1].Op == A64Op.Bl && ins[3].Op == A64Op.Bl
            ? (ins[1].Target, ins[3].Target) : null;

    internal static ulong? CallOnly(A64Instruction[] ins) =>
        ins.Length == 2 && ins[0].Word == 0xF81F0FFE && ins[1].Op == A64Op.Bl ? ins[1].Target : null;

    private static string? Literal(A64Instruction[] ins, int index, byte register, Func<ulong, string?> text)
    {
        A64Instruction page = ins[index], add = ins[index + 1];
        return page.Op == A64Op.Adrp && page.Rd == register && add.Op == A64Op.AddImm && add.Is64 && !add.SetFlags &&
            add.Rd == register && add.Rn == register && add.Imm >= 0
            ? text(page.Target + (ulong)add.Imm) : null;
    }

    private static bool Words(A64Instruction[] ins, params (int Index, uint Word)[] expected) =>
        expected.All(x => ins[x.Index].Word == x.Word);
}
