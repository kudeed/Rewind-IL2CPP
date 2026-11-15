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

    public bool Verified;

    public static KlassLayout For(int version, int pointerSize)
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
        if (version >= MetaVersion.V29_0) Ptr(); else U32(); // initializationExceptionGCHandle
        k.CctorStarted = U32();
        k.CctorFinished = U32();
        Field(8, 8);                    // cctor_thread (ALIGN_TYPE(8) size_t)
        Ptr();                          // genericContainerHandle
        k.InstanceSize = U32();
        if (version >= MetaVersion.V29_0) U32(); // stack_slot_size
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
        if (version >= MetaVersion.V24_2) U8(); // packingSize (naturalAligment in some older versions)
        k.Bitflags = U8();
        U8();                           // second bitfield byte
        k.VTable = (offset + p - 1) / p * p;
        return k;
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
