namespace Rewind.Metadata;

/// <summary>One section of global-metadata.dat. Count is the element count (derived from size before v38).</summary>
public readonly record struct MetaSection(int Offset, int Size, int Count)
{
    public int End => Offset + Size;
}

public struct ImageRow
{
    public int NameIndex, AssemblyIndex, TypeStart, ExportedTypeStart, EntryPointIndex, CustomAttributeStart;
    public uint TypeCount, ExportedTypeCount, Token, CustomAttributeCount;
    public string Name;
}

public struct AssemblyRow
{
    public int ImageIndex, ReferencedAssemblyStart, ReferencedAssemblyCount;
    public uint Token, ModuleToken;
    public int NameIndex, CultureIndex, PublicKeyIndex;
    public uint HashAlg, Flags;
    public int HashLen, Major, Minor, Build, Revision;
    public ulong PublicKeyToken;
    public string Name;
}

public struct TypeDefRow
{
    public int NameIndex, NamespaceIndex, ByvalTypeIndex, DeclaringTypeIndex, ParentIndex, ElementTypeIndex;
    public int GenericContainerIndex;
    public uint Flags;
    public int FieldStart, MethodStart, EventStart, PropertyStart, NestedTypesStart, InterfacesStart;
    public int VtableStart, InterfaceOffsetsStart;
    public ushort MethodCount, PropertyCount, FieldCount, EventCount, NestedTypeCount, VtableCount;
    public ushort InterfacesCount, InterfaceOffsetsCount;
    public uint Bitfield, Token;

    /// <summary>Only in v24.0: index into the attribute range table (later versions look up by token).</summary>
    public int CustomAttributeIndex;

    /// <summary>Only up to v24.15: runtime generic context entries stored in the metadata file.</summary>
    public int RgctxStartIndex, RgctxCount;

    public readonly bool IsValueType => (Bitfield & 1) != 0;
    public readonly bool IsEnum => (Bitfield & 2) != 0;
    public readonly bool HasFinalizer => (Bitfield & 4) != 0;
    public readonly bool HasStaticConstructor => (Bitfield & 8) != 0;
    public readonly bool IsBlittable => (Bitfield & 16) != 0;
    public readonly bool IsImportOrWindowsRuntime => (Bitfield & 32) != 0;
    public readonly int PackingSizeCode => (int)(Bitfield >> 6 & 0xF);
    public readonly bool PackingSizeIsDefault => (Bitfield >> 10 & 1) != 0;
    public readonly bool ClassSizeIsDefault => (Bitfield >> 11 & 1) != 0;
    public readonly int SpecifiedPackingSizeCode => (int)(Bitfield >> 12 & 0xF);
    public readonly bool IsByRefLike => (Bitfield >> 16 & 1) != 0;
}

public struct MethodDefRow
{
    public int NameIndex, DeclaringType, ReturnType, ParameterStart, GenericContainerIndex;
    public uint ReturnParameterToken, Token;
    public ushort Flags, ImplFlags, Slot, ParameterCount;

    /// <summary>Only in v24.0.</summary>
    public int CustomAttributeIndex;

    /// <summary>Only up to v24.15, where method pointers live in one global table.</summary>
    public int MethodIndex, InvokerIndex, DelegateWrapperIndex, RgctxStartIndex, RgctxCount;
}

public struct ParameterDefRow
{
    public int NameIndex, TypeIndex, CustomAttributeIndex;
    public uint Token;
}

public struct FieldDefRow
{
    public int NameIndex, TypeIndex, CustomAttributeIndex;
    public uint Token;
}

public struct PropertyDefRow
{
    public int NameIndex, Get, Set, CustomAttributeIndex;
    public uint Attrs, Token;
}

public struct EventDefRow
{
    public int NameIndex, TypeIndex, Add, Remove, Raise, CustomAttributeIndex;
    public uint Token;
}

public struct GenericContainerRow
{
    public int OwnerIndex, TypeArgc, IsMethod, GenericParameterStart;
}

public struct GenericParameterRow
{
    public int OwnerIndex, NameIndex;
    public short ConstraintsStart, ConstraintsCount;
    public ushort Num, Flags;
}

public struct InterfaceOffsetRow
{
    public int InterfaceTypeIndex, Offset;
}

public struct FieldRefRow
{
    public int TypeIndex, FieldIndex;
}

public struct DefaultValueRow
{
    /// <summary>Field index or parameter index, depending on the table.</summary>
    public int OwnerIndex;
    public int TypeIndex, DataIndex;
}

/// <summary>Pre-v29 attribute record: which attribute types are applied to a token.</summary>
public struct AttributeTypeRangeRow
{
    public uint Token;
    public int Start, Count;
}

/// <summary>v29+ attribute record: where the serialized attribute arguments for a token start.</summary>
public struct AttributeDataRangeRow
{
    public uint Token, StartOffset;
}

/// <summary>Pre-v27: which global slot (destination) receives which metadata item (encoded source).</summary>
public struct MetadataUsagePairRow
{
    public uint DestinationIndex, EncodedSourceIndex;
}

public struct MetadataUsageListRow
{
    public uint Start, Count;
}

/// <summary>Up to v24.15: runtime generic context entry stored in the metadata file.</summary>
public struct RgctxRow
{
    public int Type, Data;
}
