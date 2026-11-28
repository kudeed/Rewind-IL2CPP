using Rewind.Analysis.Arm64;
using Rewind.Binary;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Small, complete functions whose contracts are anchored by the image's public IL2CPP API.
/// The API's catch wrapper is not itself the throwing allocation helper. Exception factories are
/// accepted only with the exact type name, an empty message and the same public runtime operations.
/// </summary>
internal static class Arm64ExportHelperShapes
{
    internal static int Add(NativeImage image, Func<ulong, bool> isManaged, RuntimeHelpers helpers)
    {
        if (image.Arch != CpuArch.Arm64) return 0;
        // Use actual unwind extents, not the next discovered branch/call target as a function end.
        var ranges = new Dictionary<ulong, ulong>();
        foreach (FunctionRange f in image.FunctionTable)
        {
            if (f.Chained || f.End <= f.Start || isManaged(f.Start)) continue;
            if (ranges.TryGetValue(f.Start, out ulong end) && end != f.End) ranges[f.Start] = 0;
            else if (!ranges.ContainsKey(f.Start)) ranges.Add(f.Start, f.End);
        }
        A64Instruction[] Body(ulong at)
        {
            if (!ranges.TryGetValue(at, out ulong end) || end <= at || end - at > 256 || (end - at) % 4 != 0 ||
                !image.TrySpan(at, (int)(end - at), out ReadOnlySpan<byte> bytes)) return [];
            var ins = new A64Instruction[bytes.Length / 4];
            for (int i = 0; i < ins.Length; i++) ins[i] = A64Decoder.Decode(BitConverter.ToUInt32(bytes[(i * 4)..]), at + (ulong)i * 4);
            return ins;
        }
        string? Import(ulong at) => image is ElfImage elf ? elf.ImportStubs.GetValueOrDefault(at) : null;
        var sizes = ranges.Where(p => p.Value > p.Key && p.Value - p.Key <= int.MaxValue && (p.Value - p.Key) % 4 == 0)
            .ToDictionary(p => p.Key, p => (int)(p.Value - p.Key));
        Dictionary<ulong, HelperInfo> found = Identify(image.Exports, sizes, Body,
            at => ReadOnlyText(image, at), Import);
        int added = 0;
        foreach (var (at, info) in found)
            if (helpers.At(at) == null || info.ManagedStoreBarrierOnly &&
                helpers.At(at) is { Kind: HelperKind.WriteBarrier, ManagedStoreBarrierOnly: false })
            { helpers.Add(at, info); added++; }
        return added;
    }

    internal static Dictionary<ulong, HelperInfo> Identify(IReadOnlyDictionary<string, ulong> exports,
        IReadOnlyDictionary<ulong, int> sizes, Func<ulong, A64Instruction[]> body, Func<ulong, string?> text,
        Func<ulong, string?> import)
    {
        var found = new Dictionary<ulong, HelperInfo>();
        // Only an entire single-instruction B is an alias. Cycles, missing extents and argument-changing
        // wrappers are not aliases, even if their first branch happens to reach an identified helper.
        ulong Resolve(ulong at)
        {
            var seen = new HashSet<ulong>();
            for (int depth = 0; depth < 8 && sizes.TryGetValue(at, out int size) && size >= 4 && size % 4 == 0 && seen.Add(at); depth++)
            {
                if (size != 4) return at;
                A64Instruction[] ins = body(at);
                if (ins.Length != 1) return 0;
                if (ins[0].Op != A64Op.B) return at;
                at = ins[0].Target;
            }
            return 0;
        }
        ulong ExportTarget(string name) => exports.TryGetValue(name, out ulong at) ? Resolve(at) : 0;
        bool SameTarget(ulong at, ulong target) => target != 0 && Resolve(at) == target;

        ulong objectNew = 0;
        if (exports.TryGetValue("il2cpp_object_new", out ulong api) && ObjectNewTarget(body(api), import) is { } direct)
        {
            objectNew = Resolve(direct);
            if (objectNew != 0)
                found[objectNew] = new HelperInfo(HelperKind.ObjectNew, 1, false, true,
                    "object allocation (complete public API normal-path anchor)");
        }

        ulong corlib = ExportTarget("il2cpp_get_corlib"), fromName = ExportTarget("il2cpp_class_from_name"),
            init = ExportTarget("il2cpp_runtime_object_init");
        ulong raiser = exports.TryGetValue("il2cpp_raise_exception", out ulong raiseApi)
            ? PublicRaiser(body(raiseApi)) ?? 0 : 0;
        if (raiser != 0 && (!sizes.ContainsKey(raiser) || !RaisesManagedException(body(raiser), import))) raiser = 0;
        var factories = new HashSet<ulong>();
        if (objectNew != 0 && corlib != 0 && fromName != 0 && init != 0 && raiser != 0)
        {
            foreach (ulong at in sizes.Where(p => p.Value == 52).Select(p => p.Key))
            {
                A64Instruction[] ins = body(at);
                if (!IndexFactory(ins, text) || !SameTarget(ins[3].Target, corlib) ||
                    !EmptyMessageFactory(body(ins[9].Target), target => SameTarget(target, fromName),
                        target => SameTarget(target, objectNew), target => SameTarget(target, init))) continue;
                factories.Add(at);
                found[at] = new HelperInfo(HelperKind.GetIndexOutOfRangeException, 0, false, true,
                    "System.IndexOutOfRangeException factory (complete API-anchored chain)");
            }
            foreach (ulong at in sizes.Where(p => p.Value == 16).Select(p => p.Key))
                if (Arm64ExceptionChain.Raise(body(at)) is { } raise && factories.Contains(raise.Factory) && raise.Raiser == raiser)
                    found[at] = new HelperInfo(HelperKind.ThrowIndexOutOfRange, 0, true, false,
                        "System.IndexOutOfRangeException thrower (complete API-anchored chain)");
        }
        if (Arm64MarkOnlyWriteBarrierShape.Identify(exports, body) is { } dirty)
            found[dirty] = new HelperInfo(HelperKind.WriteBarrier, 1, false, false,
                "one-argument mark-only GC barrier (managed-store proof required)") { ManagedStoreBarrierOnly = true };
        for (int pass = 0; pass < 8; pass++)
        {
            int before = found.Count;
            foreach (ulong at in sizes.Where(p => p.Value is 4 or 8).Select(p => p.Key))
            {
                if (found.ContainsKey(at)) continue;
                A64Instruction[] ins = body(at);
                if (ins.Length == 1 && ins[0].Op == A64Op.B && found.TryGetValue(ins[0].Target, out HelperInfo? alias))
                    found[at] = alias with { Name = alias.Name + " (complete branch alias)" };
                else if (Arm64ExceptionChain.CallOnly(ins) is { } target && found.TryGetValue(target, out HelperInfo? called) &&
                    called is { Kind: HelperKind.ThrowIndexOutOfRange, NoReturn: true, ReturnsValue: false })
                    found[at] = called with { Name = called.Name + " (complete no-return call wrapper)" };
            }
            if (found.Count == before) break;
        }
        return found;
    }

    internal static ulong? ObjectNewTarget(A64Instruction[] ins, Func<ulong, string?> import) =>
        // The normal path returns New(klass). The separate landing pad catches and returns null;
        // only the normal-path callee is registered, never this public API wrapper.
        ins.Length == 8 && Words(ins, (0, 0xF81F0FFE), (2, 0xF84107FE), (3, 0xD65F03C0), (6, 0xAA1F03E0)) &&
        ins[1].Op == A64Op.Bl && ins[4].Op == A64Op.Bl && import(ins[4].Target) == "__cxa_begin_catch" &&
        ins[5].Op == A64Op.Bl && import(ins[5].Target) == "__cxa_end_catch" &&
        ins[7].Op == A64Op.B && ins[7].Target == ins[2].Address ? ins[1].Target : null;

    internal static ulong? PublicRaiser(A64Instruction[] ins) =>
        ins.Length == 3 && Words(ins, (0, 0xF81F0FFE), (1, 0xAA1F03E1)) && ins[2].Op == A64Op.Bl ? ins[2].Target : null;

    internal static bool RaisesManagedException(A64Instruction[] ins, Func<ulong, string?> import) =>
        // Keep the original exception across trace preparation, allocate its C++ wrapper and hand that
        // wrapper to the real noreturn runtime import. An arbitrary BL under the public name is insufficient.
        ins.Length == 10 && Words(ins, (0, 0xA9BF4FFE), (1, 0xAA0003F3), (3, 0x52800100),
            (7, 0xAA1F03E2), (8, 0xF9000013)) && ins[2].Op == A64Op.Bl &&
        ins[4].Op == A64Op.Bl && import(ins[4].Target) == "__cxa_allocate_exception" &&
        ins[5].Op == A64Op.Adrp && ins[5].Rd == 1 && ins[6].Op == A64Op.AddImm &&
        ins[6].Is64 && !ins[6].SetFlags && ins[6].Rd == 1 && ins[6].Rn == 1 && ins[6].Imm >= 0 &&
        ins[9].Op == A64Op.Bl && import(ins[9].Target) == "__cxa_throw";

    internal static string? ReadOnlyText(NativeImage image, ulong at)
    {
        ImageSection? section = image.SectionAt(at);
        if (section == null || (section.Flags & SectionFlags.Read) == 0 ||
            (section.Flags & (SectionFlags.Write | SectionFlags.Execute | SectionFlags.ZeroFill)) != 0 ||
            image.TryCString(at, 100) is not { } value || value.Length == 0 || value.Any(c => c > 127) ||
            (ulong)value.Length + 1 > section.End - at || !image.TrySpan(at, value.Length + 1, out ReadOnlySpan<byte> bytes) ||
            bytes[^1] != 0) return null;
        // Reject ambiguous mappings as well: a writable/executable alias is not an immutable type name.
        ulong end = at + (ulong)bytes.Length;
        if (image.Sections.Any(s => s.Va < end && s.End > at &&
            (s.Flags & (SectionFlags.Write | SectionFlags.Execute | SectionFlags.ZeroFill)) != 0)) return null;
        return value;
    }

    internal static bool IndexFactory(A64Instruction[] ins, Func<ulong, string?> text) =>
        ins.Length == 13 && Words(ins, (0, 0xD10083FF), (1, 0xA900FBFF), (2, 0xF90003FF),
            (8, 0x910003E3), (10, 0xF9400BFE), (11, 0x910083FF), (12, 0xD65F03C0)) &&
        ins[3].Op == A64Op.Bl && ins[9].Op == A64Op.Bl &&
        // The two ADRPs can be interleaved with the two ADDs; the registers still determine the strings.
        ((Literal(ins[4], ins[6], 1, text) == "System" && Literal(ins[5], ins[7], 2, text) == "IndexOutOfRangeException") ||
         (Literal(ins[4], ins[5], 1, text) == "System" && Literal(ins[6], ins[7], 2, text) == "IndexOutOfRangeException"));

    internal static bool EmptyMessageFactory(A64Instruction[] ins, Func<ulong, bool> fromName,
        Func<ulong, bool> objectNew, Func<ulong, bool> init) =>
        // For the proven zero-length StringView, the entire taken path is Class::FromName,
        // Object::New, Runtime::ObjectInit, return object. The other arm never runs for this factory.
        ins.Length == 19 && Words(ins, (0, 0xA9BE57FE), (1, 0xA9014FF4), (2, 0xAA0303F3),
            (5, 0xAA0003F4), (7, 0xF9400668), (9, 0xAA1303E0), (10, 0x91006295),
            (12, 0xAA0003E1), (13, 0xAA1503E0), (15, 0xAA1403E0), (16, 0xA9414FF4),
            (17, 0xA8C257FE), (18, 0xD65F03C0)) &&
        ins[3].Op == A64Op.Bl && fromName(ins[3].Target) && ins[4].Op == A64Op.Bl && objectNew(ins[4].Target) &&
        ins[6].Op == A64Op.Bl && init(ins[6].Target) &&
        ins[8].Op == A64Op.Cbz && ins[8].Is64 && ins[8].Rd == 8 && ins[8].Target == ins[15].Address &&
        ins[11].Op == A64Op.Bl && ins[14].Op == A64Op.Bl;

    private static string? Literal(A64Instruction page, A64Instruction add, byte register, Func<ulong, string?> text) =>
        page.Op == A64Op.Adrp && page.Rd == register && add.Op == A64Op.AddImm && add.Is64 && !add.SetFlags &&
        add.Rd == register && add.Rn == register && add.Imm >= 0 ? text(page.Target + (ulong)add.Imm) : null;

    private static bool Words(A64Instruction[] ins, params (int Index, uint Word)[] expected) =>
        expected.All(x => ins[x.Index].Word == x.Word);
}
