using Rewind.Analysis.Arm64;
using Rewind.Binary;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// An API-anchored GC dirty-bitmap update. The public API and its STR-and-branch callee perform a
/// reference store and are deliberately excluded. Only the complete mark-only body has one argument.
/// </summary>
internal static class Arm64MarkOnlyWriteBarrierShape
{
    internal static bool HasCompleteAliasExtent(IEnumerable<FunctionRange> functions, ulong start)
    {
        bool found = false;
        foreach (FunctionRange range in functions)
        {
            if (range.Start != start || range.Chained) continue;
            if (range.End <= start || range.End - start != 4) return false;
            found = true;
        }
        return found;
    }

    internal static ulong? Identify(IReadOnlyDictionary<string, ulong> exports, Func<ulong, A64Instruction[]> body)
    {
        if (!exports.TryGetValue("il2cpp_gc_wbarrier_set_field", out ulong api)) return null;
        A64Instruction[] wrapper = body(api);
        if (wrapper.Length != 3 || !Words(wrapper, (0, 0xAA0103E0), (1, 0xAA0203E1)) || wrapper[2].Op != A64Op.B) return null;
        A64Instruction[] store = body(wrapper[2].Target);
        if (store.Length != 2 || store[0].Word != 0xF9000001 || store[1].Op != A64Op.B) return null;
        return Matches(body(store[1].Target)) ? store[1].Target : null;
    }

    internal static bool Matches(A64Instruction[] ins) =>
        // If enabled, set the bit for the target page with a retrying exclusive update. No calls,
        // target-memory access or result production occur. x0 remains physically unchanged.
        ins.Length == 18 && ins[0].Op == A64Op.Adrp && ins[0].Rd == 8 &&
        ins[1].Op == A64Op.Ldr && !ins[1].Vector && ins[1].Size == 4 && ins[1].Rd == 8 && ins[1].Rn == 8 &&
        ins[1].Mode == A64Mode.Offset && !ins[1].Signed &&
        ins[2].Op == A64Op.Cbz && !ins[2].Is64 && ins[2].Rd == 8 && ins[2].Target == ins[17].Address &&
        ins[3].Op == A64Op.Adrp && ins[3].Rd == 10 &&
        Words(ins, (4, 0xD3528008), (5, 0x9113014A), (6, 0x528C9C0B), (7, 0xD34CFC09),
            (8, 0x72A0008B), (9, 0x5280002C), (10, 0x8B080D48), (11, 0x8B0B0108),
            (12, 0x9AC92189), (13, 0xC85F7D0A), (14, 0xAA09014A), (15, 0xC80B7D0A), (17, 0xD65F03C0)) &&
        ins[16].Op == A64Op.Cbnz && !ins[16].Is64 && ins[16].Rd == 11 && ins[16].Target == ins[13].Address;

    private static bool Words(A64Instruction[] ins, params (int Index, uint Word)[] expected) =>
        expected.All(x => ins[x.Index].Word == x.Word);
}
