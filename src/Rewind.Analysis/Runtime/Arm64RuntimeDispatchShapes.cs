using Rewind.Analysis.Arm64;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Complete ARM64 runtime contracts anchored by public IL2CPP exports. These rules do not infer an overload
/// from its name, scan past a function boundary, or treat the first RET as the end of an exception path.
/// </summary>
internal static class Arm64RuntimeDispatchShapes
{
    internal sealed record ClassInitContract(ulong GetHandleTarget, ulong Raise, ulong MetadataInitializer);

    internal static int AddClassInitializers(Il2CppModel model, ModelCodeContext context, RuntimeHelpers helpers)
    {
        // This schedule and the meaning of the flag bits have been checked against this runtime line.
        // Unknown versions and pointer-sized exception handles fail closed, even when code looks similar.
        if (model.Image.Arch != CpuArch.Arm64 || model.Image.PointerSize != 8 ||
            model.UnityVersion is not { Major: 2022, Minor: 3 }) return 0;
        var layout = KlassLayout.For(model.Version, model.Image.PointerSize, model.UnityVersion);
        if (layout.InitializationExceptionGCHandleSize != 4) return 0;
        var bodies = new CompleteBodies(model.Image, context.FunctionStarts, context.IsManaged);
        ulong? Export(string name) => model.Image.Exports.TryGetValue(name, out ulong address) ? address : null;
        string? Import(ulong address) => model.Image is ElfImage elf ? elf.ImportStubs.GetValueOrDefault(address) : null;
        bool Data(ulong address) => model.Image.IsMapped(address, 8) && model.Image.IsDataAddress(address);
        bool ReadOnlyPointer(ulong address) => model.Image.IsReadOnlyAfterLoad(address) &&
            model.Image.TryPtr(address, out ulong value) && Data(value);
        ClassInitContract? known = FromExports(Export, bodies.Read, Import, Data);
        if (known == null) return 0;
        int added = 0;
        foreach (ulong start in bodies.StartsOfSize(44))
        {
            if (context.IsManaged(start) || helpers.At(start) != null) continue;
            if (!IsClassInitOneArgument(bodies.Read(start), layout, known, bodies.Read, ReadOnlyPointer)) continue;
            helpers.Add(start, new HelperInfo(HelperKind.ClassInitSlow, 1, false, true,
                "one-argument class metadata initialization (complete ARM64 export-anchored shape)"));
            added++;
        }
        return added;
    }

    internal static ClassInitContract? FromExports(Func<string, ulong?> export,
        Func<ulong, A64Instruction[]> body, Func<ulong, string?> import, Func<ulong, bool> data)
    {
        if (export("il2cpp_gchandle_get_target") is not { } getterExport ||
            export("il2cpp_raise_exception") is not { } raiseExport ||
            export("il2cpp_class_from_system_type") is not { } systemTypeExport ||
            export("il2cpp_class_from_il2cpp_type") is not { } nativeTypeExport) return null;
        A64Instruction[] getter = body(getterExport), raise = body(raiseExport);
        if (getter.Length != 1 || getter[0].Op != A64Op.B || getter[0].Target == getterExport ||
            body(getter[0].Target).Length == 0 ||
            raise.Length != 3 || !Words(raise, (0, 0xF81F0FFE), (1, 0xAA1F03E1)) ||
            raise[2].Op != A64Op.Bl || raise[2].Target == raiseExport) return null;
        A64Instruction[] endpoint = body(raise[2].Target);
        // The public API establishes the raiser's role. Its entire body also establishes no-return:
        // wrap the same managed exception, allocate an 8-byte C++ exception, and call __cxa_throw.
        if (endpoint.Length != 10 || !Words(endpoint, (0, 0xA9BF4FFE), (1, 0xAA0003F3),
                (3, 0x52800100), (7, 0xAA1F03E2), (8, 0xF9000013)) ||
            endpoint[2].Op != A64Op.Bl || body(endpoint[2].Target).Length == 0 ||
            endpoint[4].Op != A64Op.Bl || import(endpoint[4].Target) != "__cxa_allocate_exception" ||
            endpoint[9].Op != A64Op.Bl || import(endpoint[9].Target) != "__cxa_throw" ||
            Literal(endpoint[5], endpoint[6], 1) is not { } typeInfo || !data(typeInfo)) return null;
        // The initializer is independently anchored by the public System.Type conversion API. The first
        // call converts RuntimeType.type with throwOnError=true through the exact native-type export target;
        // the second initializes that resulting class, then the API returns the same class unchanged.
        A64Instruction[] systemType = body(systemTypeExport), nativeType = body(nativeTypeExport);
        if (systemType.Length != 1 || systemType[0].Op != A64Op.B || systemType[0].Target == systemTypeExport ||
            nativeType.Length != 2 || nativeType[0].Word != 0x52800021 || nativeType[1].Op != A64Op.B ||
            nativeType[1].Target == nativeTypeExport) return null;
        A64Instruction[] convert = body(systemType[0].Target);
        if (convert.Length != 9 || !Words(convert, (0, 0xA9BF4FFE), (1, 0xF9400800), (2, 0x52800021),
                (4, 0xAA0003F3), (6, 0xAA1303E0), (7, 0xA8C14FFE), (8, 0xD65F03C0)) ||
            convert[3].Op != A64Op.Bl || convert[3].Target != nativeType[1].Target ||
            convert[5].Op != A64Op.Bl || convert[5].Target == convert[3].Target ||
            body(convert[5].Target).Length != 22) return null;
        return new ClassInitContract(getter[0].Target, raise[2].Target, convert[5].Target);
    }

    internal static bool IsClassInitOneArgument(A64Instruction[] ins, KlassLayout layout, ClassInitContract known,
        Func<ulong, A64Instruction[]> body, Func<ulong, bool> readOnlyPointer)
    {
        // Exactly one argument. In particular, the (klass, bool throwOnError) overload can return null;
        // it is not interchangeable with this helper and cannot match the complete schedule below.
        return layout.InitializationExceptionGCHandleSize == 4 && ins.Length == 11 &&
            Words(ins, (0, 0xA9BF4FFE), (1, 0xAA0003F3), (5, 0xAA1303E0),
                (6, 0xA8C14FFE), (7, 0xD65F03C0), (9, 0xAA1F03E1)) &&
            ins[2].Op == A64Op.Bl && ins[2].Target == known.MetadataInitializer &&
            IsMetadataInitializer(body(ins[2].Target), layout, body, readOnlyPointer) &&
            Load(ins[3], 0, 19, 4, layout.InitializationExceptionGCHandle) &&
            ins[4].Op == A64Op.Cbnz && !ins[4].Is64 && ins[4].Rd == 0 && ins[4].Target == ins[8].Address &&
            ins[8].Op == A64Op.Bl && ins[8].Target == known.GetHandleTarget &&
            ins[10].Op == A64Op.Bl && ins[10].Target == known.Raise;
    }

    internal static bool IsMetadataInitializer(A64Instruction[] ins, KlassLayout layout,
        Func<ulong, A64Instruction[]> body, Func<ulong, bool> readOnlyPointer)
    {
        // Full initialized-bit check, lock object lifetime, InitLocked(klass, lock), and EH cleanup.
        // The success and exceptional exits must release the same lock using the same callee.
        if (ins.Length != 22 || !Words(ins, (0, 0xD10083FF), (1, 0xA9014FFE),
                (6, 0xAA0003F3), (7, 0x910023E0), (9, 0x910023E1), (10, 0xAA1303E0),
                (12, 0x910023E0), (14, 0xA9414FFE), (15, 0x910083FF), (16, 0xD65F03C0),
                (17, 0xAA0003F3), (18, 0x910023E0), (20, 0xAA1303E0)) ||
            !Load(ins[2], 8, 0, 1, layout.Bitflags) ||
            ins[3].Op != A64Op.Tbnz || ins[3].Rd != 8 || ins[3].Imm != 1 ||
            ins[3].Target != ins[14].Address ||
            ins[4].Op != A64Op.Adrp || ins[4].Rd != 1 ||
            !Load(ins[5], 1, 1, 8, ins[5].Imm) || ins[5].Imm < 0 ||
            ins[4].Target > ulong.MaxValue - (ulong)ins[5].Imm ||
            !readOnlyPointer(ins[4].Target + (ulong)ins[5].Imm)) return false;
        int[] calls = [8, 11, 13, 19, 21];
        if (calls.Any(i => ins[i].Op != A64Op.Bl || body(ins[i].Target).Length == 0) ||
            ins[13].Target != ins[19].Target ||
            new[] { ins[8].Target, ins[11].Target, ins[13].Target, ins[21].Target }.Distinct().Count() != 4)
            return false;
        return true;
    }

    private static bool Load(A64Instruction ins, byte destination, byte receiver, byte size, long offset) =>
        ins.Op == A64Op.Ldr && !ins.Vector && !ins.Signed && ins.Mode == A64Mode.Offset &&
        ins.Rd == destination && ins.Rn == receiver && ins.Size == size && ins.Imm == offset;

    private static ulong? Literal(A64Instruction page, A64Instruction add, byte register) =>
        page.Op == A64Op.Adrp && page.Rd == register && add.Op == A64Op.AddImm && add.Is64 && !add.SetFlags &&
        add.Rd == register && add.Rn == register && add.Imm >= 0 && page.Target <= ulong.MaxValue - (ulong)add.Imm
            ? page.Target + (ulong)add.Imm : null;

    private static bool Words(A64Instruction[] ins, params (int Index, uint Word)[] expected) =>
        expected.All(x => ins[x.Index].Word == x.Word);

    /// <summary>Reads exact unwind extents; a prefix or a neighbouring function can never supply missing code.</summary>
    internal sealed class CompleteBodies
    {
        private readonly NativeImage _image;
        private readonly Dictionary<ulong, FunctionRange> _ranges;
        private readonly ulong[] _entries;
        private readonly Func<ulong, bool> _managed;
        private readonly Dictionary<ulong, A64Instruction[]> _cache = [];

        internal CompleteBodies(NativeImage image, IEnumerable<ulong> entries, Func<ulong, bool> managed)
        {
            _image = image;
            _entries = entries.Distinct().Order().ToArray();
            _managed = managed;
            _ranges = image.FunctionTable.GroupBy(x => x.Start)
                .Where(g => g.Count() == 1 && !g.Single().Chained).ToDictionary(g => g.Key, g => g.Single());
        }

        internal IEnumerable<ulong> StartsOfSize(int bytes) =>
            _ranges.Values.Where(r => r.End > r.Start && r.End - r.Start == (ulong)bytes).Select(r => r.Start);

        internal A64Instruction[] Read(ulong start)
        {
            if (_cache.TryGetValue(start, out A64Instruction[]? cached)) return cached;
            return _cache[start] = ReadUncached(start);
        }

        private A64Instruction[] ReadUncached(ulong start)
        {
            if (_managed(start) || !_ranges.TryGetValue(start, out FunctionRange range) || range.End <= start ||
                (start & 3) != 0 || range.End - start is > 4096 || ((range.End - start) & 3) != 0) return [];
            int next = Array.BinarySearch(_entries, start);
            next = next >= 0 ? next + 1 : ~next;
            if (next < _entries.Length && _entries[next] < range.End) return [];
            int length = (int)(range.End - start);
            if (_image.SectionAt(start) is not { IsExecutable: true } section || range.End > section.End ||
                !_image.TrySpan(start, length, out ReadOnlySpan<byte> bytes)) return [];
            var result = new A64Instruction[length / 4];
            for (int i = 0; i < result.Length; i++)
            {
                result[i] = A64Decoder.Decode(BitConverter.ToUInt32(bytes[(i * 4)..]), start + (ulong)i * 4);
                if (result[i].IsInvalid || result[i].Op == A64Op.Unknown) return [];
            }
            return result;
        }
    }
}
