using Iced.Intel;
using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Model;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Offsets of the Il2CppClass fields that generated code reads directly. Computed from the struct definition
/// in libil2cpp's il2cpp-class-internals.h for the pointer size in use.
/// </summary>
public sealed class KlassLayout
{
    public int ElementClass, CastClass, DeclaringType, Parent, GenericClass, InterfaceOffsets, StaticFields, RgctxData,
        TypeHierarchy, CctorStarted, CctorFinished, InstanceSize, ElementSize, Flags, VTableCount, InterfaceOffsetsCount,
        TypeHierarchyDepth, Rank, Bitflags, VTable, ByvalArg, ThisArg;

    /// <summary>Size of one vtable entry: { method pointer, MethodInfo* }.</summary>
    public int VTableEntrySize;

    /// <summary>
    /// Unity before 2021.2 guards a static constructor with two tests, "has_cctor &amp;&amp; !cctor_finished": the byte
    /// that holds the has_cctor bit and the bit's mask. 0 where generated code makes one test only
    /// ("!cctor_finished_or_no_cctor").
    /// </summary>
    public int HasCctorByte, HasCctorMask;

    /// <summary>What decided the offsets that differ between Unity versions: the version alone, or the game's own code.</summary>
    public string Source = "version";

    /// <summary>
    /// The parts of the record that changed between Unity versions without the metadata version saying so
    /// (checked against the headers of 2020.3.49, 2021.3.45, 2022.3.62, 6000.0.85, 6000.2.9 and 6000.3.12):
    /// initializationExceptionGCHandle is 32 bits wide through 2022.3 and a pointer from Unity 6, which moves
    /// cctor_started and cctor_finished by four bytes; stack_slot_size (2022.3 and later, not 2021.3) moves
    /// everything behind instance_size by four bytes; naturalAligment (2020.3 and 2021.3, gone in 2022.3) moves the
    /// flag bits by one.
    /// </summary>
    private readonly record struct Shape(bool HandleIsPointer, bool StackSlotSize, bool NaturalAlignment);

    private static Shape ShapeOf(int version, UnityVersion? unity)
    {
        if (unity is { } u)
        {
            // Where between the checked versions each change happened is not known; it is put at the start of the
            // newer line here, and Measure corrects it where a game's code says otherwise.
            bool newer = u.AtLeast(2022, 2);
            return new Shape(u.Major >= 6000, newer, !newer && version >= MetaVersion.V27_0);
        }
        // Without the Unity version, the metadata version alone (31.0 is the format of late 2021.3 builds).
        bool late = version >= MetaVersion.V31_1 || version == MetaVersion.V29_1;
        return new Shape(version >= MetaVersion.V35, late, !late && version >= MetaVersion.V27_0);
    }

    public static KlassLayout For(int version, int pointerSize, UnityVersion? unity = null) =>
        Build(version, pointerSize, ShapeOf(version, unity));

    private static KlassLayout Build(int version, int pointerSize, Shape shape)
    {
        int p = pointerSize;
        int offset = 0;

        int Field(int size, int align)
        {
            offset = (offset + align - 1) / align * align;
            int at = offset;
            offset += size;
            return at;
        }
        int Ptr() => Field(p, p);
        int U32() => Field(4, 4);
        int U16() => Field(2, 2);
        int U8() => Field(1, 1);
        int Il2CppType() => Field(p + 4 + (p == 8 ? 4 : 0), p); // data pointer + 32 bits of flags, padded

        var k = new KlassLayout { VTableEntrySize = 2 * p };
        Ptr();                          // image
        Ptr();                          // gc_desc
        Ptr();                          // name
        Ptr();                          // namespaze
        k.ByvalArg = Il2CppType();
        k.ThisArg = Il2CppType();
        k.ElementClass = Ptr();
        k.CastClass = Ptr();
        k.DeclaringType = Ptr();
        k.Parent = Ptr();
        k.GenericClass = Ptr();
        Ptr();                          // typeMetadataHandle
        Ptr();                          // interopData
        Ptr();                          // klass
        Ptr();                          // fields
        Ptr();                          // events
        Ptr();                          // properties
        Ptr();                          // methods
        Ptr();                          // nestedTypes
        Ptr();                          // implementedInterfaces
        k.InterfaceOffsets = Ptr();
        k.StaticFields = Ptr();
        k.RgctxData = Ptr();
        k.TypeHierarchy = Ptr();
        Ptr();                          // unity_user_data
        if (shape.HandleIsPointer) Ptr(); else U32(); // initializationExceptionGCHandle
        k.CctorStarted = U32();
        k.CctorFinished = U32();
        Field(8, 8);                    // cctor_thread (ALIGN_TYPE(8) size_t)
        Ptr();                          // genericContainerHandle
        k.InstanceSize = U32();
        if (shape.StackSlotSize) U32(); // stack_slot_size
        U32();                          // actualSize
        k.ElementSize = U32();
        U32();                          // native_size
        U32();                          // static_fields_size
        U32();                          // thread_static_fields_size
        U32();                          // thread_static_fields_offset
        k.Flags = U32();
        U32();                          // token
        U16();                          // method_count
        U16();                          // property_count
        U16();                          // field_count
        U16();                          // event_count
        U16();                          // nested_type_count
        k.VTableCount = U16();
        U16();                          // interfaces_count
        k.InterfaceOffsetsCount = U16();
        k.TypeHierarchyDepth = U8();
        U8();                           // genericRecursionDepth
        k.Rank = U8();
        U8();                           // minimumAlignment
        if (shape.NaturalAlignment) U8(); // naturalAligment
        if (version >= MetaVersion.V24_2) U8(); // packingSize
        k.Bitflags = U8();
        U8();                           // second bitfield byte
        k.VTable = (offset + p - 1) / p * p;
        if (version < MetaVersion.V29_0)
        {
            // Second flag byte: size_inited, has_finalize, has_cctor, ...
            k.HasCctorByte = k.Bitflags + 1;
            k.HasCctorMask = 4;
        }
        return k;
    }

    /// <summary>
    /// The same reads in A64 code: a 32-bit field tested for zero ("ldr w, [klass, #d]; cbz/cbnz"), a flag byte's
    /// bit tested ("ldrb w, [klass, #d]; tbz/tbnz w, #bit"), 16-bit and byte fields read.
    /// </summary>
    private static void CountArm64(NativeImage image, int span, int[] compared, int[] words, int[] bytes, int[] firstBit,
        Dictionary<(int Compared, int Byte, int Mask), int> guards)
    {
        foreach (FunctionRange f in image.FunctionTable)
        {
            // What was loaded into each register lately: (base register, offset, size, where).
            var loaded = new (byte Base, int Offset, int Size, ulong At)[32];
            byte testedBase = 255;
            int testedByte = 0, testedMask = 0;
            ulong testedAt = 0;
            for (ulong at = f.Start; at + 4 <= f.End && image.IsMapped(at, 4); at += 4)
            {
                Arm64.A64Instruction ins = Arm64.A64Decoder.Decode(image.U32(at), at);
                if (ins.IsInvalid) break;
                if (ins.Op == Arm64.A64Op.Ldr && !ins.Vector && !ins.Signed && ins.Mode == Arm64.A64Mode.Offset && ins.Rd < 31 &&
                    ins.Rn < 31 && ins.Imm is >= 0 && ins.Imm < span)
                {
                    int d = (int)ins.Imm;
                    if (ins.Size == 2) words[d]++;
                    if (ins.Size == 1) bytes[d]++;
                    loaded[ins.Rd] = (ins.Rn, d, ins.Size, at);
                    continue;
                }
                if (ins.Op is Arm64.A64Op.Cbz or Arm64.A64Op.Cbnz && ins.Rd < 31 && loaded[ins.Rd] is { Size: 4, At: not 0 } word && at - word.At <= 8)
                {
                    compared[word.Offset]++;
                    if (testedBase == word.Base && at - testedAt <= 16)
                    {
                        var key = (word.Offset, testedByte, testedMask);
                        guards[key] = guards.GetValueOrDefault(key) + 1;
                    }
                }
                if (ins.Op is Arm64.A64Op.Tbz or Arm64.A64Op.Tbnz && ins.Rd < 31 && loaded[ins.Rd] is { Size: 1, At: not 0 } flag && at - flag.At <= 8 && ins.Imm < 8)
                {
                    if (ins.Imm == 0) firstBit[flag.Offset]++;
                    (testedBase, testedByte, testedMask, testedAt) = (flag.Base, flag.Offset, 1 << (int)ins.Imm, at);
                }
                for (byte r = 0; r < 31; r++)
                    if (loaded[r].At != 0 && Arm64.A64Cfg.Writes(ins, r)) loaded[r] = default;
            }
        }
    }

    /// <summary>How often one candidate must be read, and how many times as often as the other, to be taken.</summary>
    private const int MinimumEvidence = 16, EvidenceMargin = 8;

    /// <summary>
    /// The layout for the game's version, corrected by what the game's own code reads. Generated code tests
    /// cctor_finished before every use of a class's statics, reads interface_offsets_count and typeHierarchyDepth
    /// for interface calls and casts, and tests the first flag bit (initialized_and_no_error) before using a
    /// class it looked up: where the two possible places of such a field are read very unequally often, the one
    /// the code reads is where the field is. That settles versions whose headers could not be checked, and a
    /// game whose Unity version is not known.
    /// </summary>
    public static KlassLayout Measure(Il2CppModel model, Action<string>? log = null)
    {
        NativeImage image = model.Image;
        int p = image.PointerSize;
        Shape shape = ShapeOf(model.Version, model.UnityVersion);
        KlassLayout byVersion = Build(model.Version, p, shape);
        if (image.Arch is not (CpuArch.X64 or CpuArch.Arm64)) return byVersion;

        // How often each offset near the fields in question is read, by the kind of read.
        const int Span = 0x200;
        int[] compared = new int[Span], words = new int[Span], bytes = new int[Span], firstBit = new int[Span];
        // (offset compared, byte offset, mask) of a bit tested just before a 32-bit compare on the same class.
        var guards = new Dictionary<(int Compared, int Byte, int Mask), int>();

        if (image.Arch == CpuArch.Arm64) CountArm64(image, Span, compared, words, bytes, firstBit, guards);
        else foreach (FunctionRange f in image.FunctionTable)
        {
            int length = (int)(f.End - f.Start);
            if (length <= 0 || !image.TrySpan(f.Start, length, out ReadOnlySpan<byte> code)) continue;
            var decoder = Decoder.Create(64, new ByteArrayCodeReader(code.ToArray()), f.Start);
            Register testedBase = Register.None;
            int testedByte = 0, testedMask = 0, sinceTest = int.MaxValue;
            while (decoder.IP < f.End)
            {
                decoder.Decode(out Instruction ins);
                if (ins.IsInvalid) break;
                if (sinceTest != int.MaxValue) sinceTest++;
                if (ins.MemoryBase is Register.None or Register.RSP or Register.RBP or Register.RIP || ins.MemoryIndex != Register.None) continue;
                if (ins.MemoryDisplacement64 >= Span) continue;
                int d = (int)ins.MemoryDisplacement64;
                switch (ins.Mnemonic)
                {
                    case Mnemonic.Cmp when ins.Op0Kind == OpKind.Memory && ins.MemorySize is MemorySize.UInt32 or MemorySize.Int32:
                        compared[d]++;
                        if (sinceTest <= 3 && ins.MemoryBase == testedBase)
                        {
                            var key = (d, testedByte, testedMask);
                            guards[key] = guards.GetValueOrDefault(key) + 1;
                        }
                        break;
                    case Mnemonic.Test when ins.Op0Kind == OpKind.Memory && ins.MemorySize is MemorySize.UInt8 or MemorySize.Int8 && ins.Op1Kind == OpKind.Immediate8:
                        if (ins.Immediate8 == 1) firstBit[d]++;
                        (testedBase, testedByte, testedMask, sinceTest) = (ins.MemoryBase, d, ins.Immediate8, 0);
                        break;
                    case Mnemonic.Movzx when ins.Op1Kind == OpKind.Memory && ins.MemorySize is MemorySize.UInt16 or MemorySize.Int16:
                        words[d]++;
                        break;
                    case Mnemonic.Movzx when ins.Op1Kind == OpKind.Memory && ins.MemorySize is MemorySize.UInt8 or MemorySize.Int8:
                        bytes[d]++;
                        break;
                }
            }
        }

        static bool Clear(int winner, int loser) => winner >= MinimumEvidence && winner >= EvidenceMargin * Math.Max(1, loser);
        var notes = new List<string>();
        bool confirmed = false, changed = false;
        // One question at a time, each with the answers before it in place: is the field where the layout has it,
        // or where it would be with the one thing changed?
        Shape Settle(Shape current, Shape other, Func<KlassLayout, int> reads, string what, Func<KlassLayout, int> at)
        {
            KlassLayout here = Build(model.Version, p, current), there = Build(model.Version, p, other);
            int readsHere = reads(here), readsThere = reads(there);
            if (Clear(readsThere, readsHere))
            {
                changed = true;
                notes.Add($"{what} at 0x{at(there):X} (read {readsThere} times, 0x{at(here):X} {readsHere} times)");
                return other;
            }
            if (Clear(readsHere, readsThere)) confirmed = true;
            notes.Add($"{what} at 0x{at(here):X} (read {readsHere} times, 0x{at(there):X} {readsThere} times)");
            return current;
        }
        shape = Settle(shape, shape with { HandleIsPointer = !shape.HandleIsPointer }, k => compared[k.CctorFinished], "cctor_finished", k => k.CctorFinished);
        shape = Settle(shape, shape with { StackSlotSize = !shape.StackSlotSize }, k => words[k.InterfaceOffsetsCount] + bytes[k.TypeHierarchyDepth],
            "interface_offsets_count", k => k.InterfaceOffsetsCount);
        shape = Settle(shape, shape with { NaturalAlignment = !shape.NaturalAlignment }, k => firstBit[k.Bitflags], "flag bits", k => k.Bitflags);
        KlassLayout layout = Build(model.Version, p, shape);
        if (changed) layout.Source = "the game's code (not as the version's layout has it)";
        else if (confirmed) layout.Source = "the version's layout, confirmed by the game's code";

        // The has_cctor test: the bit tested right before cctor_finished nearly every time, or no such test at all.
        int finished = compared[layout.CctorFinished];
        if (finished >= MinimumEvidence)
        {
            var guard = guards.Where(g => g.Key.Compared == layout.CctorFinished).OrderByDescending(g => g.Value).FirstOrDefault();
            if (guard.Value >= MinimumEvidence && guard.Value * 2 >= finished)
            {
                (layout.HasCctorByte, layout.HasCctorMask) = (guard.Key.Byte, guard.Key.Mask);
                notes.Add($"has_cctor bit 0x{guard.Key.Mask:X} at 0x{guard.Key.Byte:X} (tested before cctor_finished {guard.Value} times)");
            }
            else (layout.HasCctorByte, layout.HasCctorMask) = (0, 0);
        }
        log?.Invoke($"class record layout from {layout.Source}: {string.Join("; ", notes)}");
        return layout;
    }
}

/// <summary>
/// The runtime's table of well-known classes (il2cpp_defaults). Generated code reads classes such as
/// System.Int32 from fixed slots of this table instead of going through a metadata usage slot.
/// </summary>
public sealed class DefaultsTable
{
    /// <summary>Slot address to the type whose class pointer the slot holds.</summary>
    public Dictionary<ulong, TypeDef> Slots { get; } = [];

    /// <summary>
    /// Finds the slots by reading the runtime's own initialization code, which does, for each well-known type,
    /// <c>slot = Class::FromName(corlib, "Namespace", "Name")</c>. Works without symbols.
    /// </summary>
    public static DefaultsTable Locate(Il2CppModel model)
    {
        var table = new DefaultsTable();
        NativeImage image = model.Image;
        if (image.Arch == CpuArch.Arm64) return LocateArm64(model, table);
        if (image.Arch != CpuArch.X64) return table;

        var managed = new HashSet<ulong>(model.MethodsByAddress.Keys);
        foreach (ImageSection section in image.Sections)
        {
            if (!section.IsExecutable || !image.IsMapped(section.Va)) continue;
            // Managed code lives in its own section on Windows; the initializer is in the runtime's section.
            if (section.Name == "il2cpp") continue;
            byte[] code = image.SpanToSectionEnd(section.Va).ToArray();
            var decoder = Decoder.Create(64, new ByteArrayCodeReader(code), section.Va);
            ulong end = section.Va + (ulong)code.Length;

            string? ns = null, name = null;
            int sinceCall = int.MaxValue;
            string? pendingNs = null, pendingName = null;
            while (decoder.IP < end)
            {
                decoder.Decode(out Instruction ins);
                if (ins.IsInvalid) continue;
                sinceCall = sinceCall == int.MaxValue ? int.MaxValue : sinceCall + 1;

                if (ins.Mnemonic == Mnemonic.Lea && ins.IsIPRelativeMemoryOperand && ins.Op0Kind == OpKind.Register)
                {
                    string? text = ReadIdentifier(image, ins.IPRelativeMemoryAddress);
                    if (text != null)
                    {
                        if (ins.Op0Register == Register.RDX) ns = text;
                        else if (ins.Op0Register == Register.R8) name = text;
                    }
                }
                else if (ins.Mnemonic == Mnemonic.Call)
                {
                    pendingNs = ns;
                    pendingName = name;
                    ns = name = null;
                    sinceCall = 0;
                }
                else if (ins.Mnemonic == Mnemonic.Mov && ins.Op0Kind == OpKind.Memory && ins.IsIPRelativeMemoryOperand &&
                         ins.Op1Kind == OpKind.Register && ins.Op1Register == Register.RAX && sinceCall <= 3 &&
                         pendingNs != null && pendingName != null)
                {
                    TypeDef? type = model.FindType(pendingNs.Length == 0 ? pendingName : pendingNs + "." + pendingName);
                    ulong slot = ins.IPRelativeMemoryAddress;
                    if (type != null && image.SectionAt(slot) is { IsWritable: true }) table.Slots.TryAdd(slot, type);
                    pendingNs = pendingName = null;
                }
            }
        }
        _ = managed;
        return table;
    }

    /// <summary>
    /// The same for AArch64: "adrp/add x1, namespace; adrp/add x2, name; bl Class::FromName; str x0, [base, #slot]",
    /// with the addresses the registers hold followed through ADRP, ADD and loads from the GOT.
    /// </summary>
    private static DefaultsTable LocateArm64(Il2CppModel model, DefaultsTable table)
    {
        NativeImage image = model.Image;
        foreach (ImageSection section in image.Sections)
        {
            if (!section.IsExecutable || section.Name == "il2cpp" || !image.IsMapped(section.Va)) continue;
            var constant = new ulong?[32];
            string? pendingNs = null, pendingName = null;
            int sinceCall = int.MaxValue;
            for (ulong at = section.Va; at + 4 <= section.End && image.IsMapped(at, 4); at += 4)
            {
                Arm64.A64Instruction ins = Arm64.A64Decoder.Decode(image.U32(at), at);
                if (sinceCall != int.MaxValue) sinceCall++;
                switch (ins.Op)
                {
                    case Arm64.A64Op.Adrp or Arm64.A64Op.Adr:
                        constant[ins.Rd] = ins.Target;
                        continue;
                    case Arm64.A64Op.AddImm when !ins.SetFlags && ins.Rn < 31 && ins.Rd < 31 && constant[ins.Rn] is ulong page:
                        constant[ins.Rd] = page + (ulong)ins.Imm;
                        continue;
                    case Arm64.A64Op.Ldr when !ins.Vector && ins.Size == 8 && ins.Mode == Arm64.A64Mode.Offset && ins.Rn < 31 && ins.Rd < 31 &&
                                               constant[ins.Rn] is ulong got && image.IsReadOnlyAfterLoad(got + (ulong)ins.Imm):
                        constant[ins.Rd] = image.U64(got + (ulong)ins.Imm);
                        continue;
                    case Arm64.A64Op.Bl or Arm64.A64Op.Blr:
                    {
                        string? ns = constant[1] is ulong n ? ReadIdentifier(image, n) : null;
                        string? name = constant[2] is ulong m ? ReadIdentifier(image, m) : null;
                        (pendingNs, pendingName) = (ns, name);
                        sinceCall = 0;
                        for (int r = 0; r <= 18; r++) constant[r] = null;
                        constant[30] = null;
                        continue;
                    }
                    case Arm64.A64Op.Str when !ins.Vector && ins.Size == 8 && ins.Rd == 0 && ins.Mode == Arm64.A64Mode.Offset && ins.Rn < 31 &&
                                               constant[ins.Rn] is ulong baseAddress && sinceCall <= 3 && pendingNs != null && pendingName != null:
                    {
                        TypeDef? type = model.FindType(pendingNs.Length == 0 ? pendingName : pendingNs + "." + pendingName);
                        ulong slot = baseAddress + (ulong)ins.Imm;
                        if (type != null && image.SectionAt(slot) is { IsWritable: true }) table.Slots.TryAdd(slot, type);
                        pendingNs = pendingName = null;
                        continue;
                    }
                    case Arm64.A64Op.B or Arm64.A64Op.Br or Arm64.A64Op.Ret:
                        Array.Clear(constant);
                        continue;
                }
                for (byte r = 0; r < 31; r++)
                    if (constant[r] != null && Arm64.A64Cfg.Writes(ins, r)) constant[r] = null;
            }
        }
        return table;
    }

    private static string? ReadIdentifier(NativeImage image, ulong va)
    {
        ImageSection? section = image.SectionAt(va);
        if (section == null || section.IsExecutable || section.IsWritable) return null;
        string? s = image.TryCString(va, 96);
        if (s == null || s.Length == 0 || s.Length > 80) return null;
        foreach (char c in s)
            if (!(char.IsAsciiLetterOrDigit(c) || c is '.' or '_' or '`'))
                return null;
        return s;
    }
}
