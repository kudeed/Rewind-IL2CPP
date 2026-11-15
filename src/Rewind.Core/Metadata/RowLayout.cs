using System.Buffers.Binary;
using System.Runtime.CompilerServices;

namespace Rewind.Metadata;

public enum FieldKind : byte
{
    I32, U32, I16, U16,
    /// <summary>Index into the binary's Il2CppType table; 1, 2 or 4 bytes wide from v38.</summary>
    TypeIndex,
    /// <summary>Index into the type definition table; variable width from v38.</summary>
    TypeDefIndex,
    /// <summary>Index into the generic container table; variable width from v38.</summary>
    GenericContainerIndex,
    /// <summary>Index into the parameter table; variable width from v39.</summary>
    ParameterIndex,
    Bytes8,
}

/// <summary>Serialized widths of the index kinds that became variable-width in metadata v38/v39.</summary>
public readonly record struct IndexWidths(int Type, int TypeDef, int GenericContainer, int Parameter)
{
    public static readonly IndexWidths Fixed = new(4, 4, 4, 4);

    /// <summary>Unity's GetIndexSize: the smallest of 1, 2 or 4 bytes that can address the table.</summary>
    public static int ForCount(int count) => count <= byte.MaxValue ? 1 : count <= ushort.MaxValue ? 2 : 4;

    public int Of(FieldKind kind) => kind switch
    {
        FieldKind.TypeIndex => Type,
        FieldKind.TypeDefIndex => TypeDef,
        FieldKind.GenericContainerIndex => GenericContainer,
        FieldKind.ParameterIndex => Parameter,
        FieldKind.I16 or FieldKind.U16 => 2,
        FieldKind.Bytes8 => 8,
        _ => 4,
    };
}

/// <summary>Reads one field of a serialized row; knows whether the field exists in the active layout.</summary>
public readonly struct FieldAccessor
{
    public readonly int Offset;
    public readonly byte Width;
    public readonly FieldKind Kind;
    private readonly int _missing;

    public FieldAccessor(int offset, int width, FieldKind kind, int missing)
    {
        Offset = offset;
        Width = (byte)width;
        Kind = kind;
        _missing = missing;
    }

    public bool Exists => Offset >= 0;

    private bool IsIndex => Kind is FieldKind.TypeIndex or FieldKind.TypeDefIndex
        or FieldKind.GenericContainerIndex or FieldKind.ParameterIndex;

    /// <summary>Value as a signed int. Narrow indexes map their all-ones value to -1, as libil2cpp does.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public int Int(ReadOnlySpan<byte> row)
    {
        if (Offset < 0) return _missing;
        switch (Width)
        {
            case 1:
            {
                byte v = row[Offset];
                return IsIndex && v == byte.MaxValue ? -1 : v;
            }
            case 2:
            {
                ushort v = BinaryPrimitives.ReadUInt16LittleEndian(row.Slice(Offset, 2));
                if (Kind == FieldKind.I16) return (short)v;
                return IsIndex && v == ushort.MaxValue ? -1 : v;
            }
            default:
                return BinaryPrimitives.ReadInt32LittleEndian(row.Slice(Offset, 4));
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public uint UInt(ReadOnlySpan<byte> row) => (uint)Int(row);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public ushort UShort(ReadOnlySpan<byte> row) => (ushort)Int(row);
}

public sealed class RowLayout
{
    private readonly Dictionary<string, FieldAccessor> _fields;

    public int Size { get; }
    public string Name { get; }

    internal RowLayout(string name, int size, Dictionary<string, FieldAccessor> fields)
    {
        Name = name;
        Size = size;
        _fields = fields;
    }

    public bool Has(string field) => _fields.ContainsKey(field);

    /// <summary>Accessor for a field; when the layout lacks the field, reads return <paramref name="missing"/>.</summary>
    public FieldAccessor Field(string field, int missing = 0) =>
        _fields.TryGetValue(field, out FieldAccessor f) ? f : new FieldAccessor(-1, 4, FieldKind.I32, missing);
}

/// <summary>Builds a row layout for one metadata version from a field list annotated with version ranges.</summary>
public sealed class RowLayoutBuilder
{
    private readonly string _name;
    private readonly int _version;
    private readonly IndexWidths _widths;
    private readonly Dictionary<string, FieldAccessor> _fields = new(StringComparer.Ordinal);
    private int _offset;

    public RowLayoutBuilder(string name, int version, IndexWidths widths)
    {
        _name = name;
        _version = version;
        _widths = widths;
    }

    /// <summary>Adds a field present in versions <paramref name="min"/>..<paramref name="max"/> inclusive.</summary>
    public RowLayoutBuilder Add(string field, FieldKind kind = FieldKind.I32, int min = 0, int max = int.MaxValue)
    {
        if (_version < min || _version > max) return this;
        int width = _widths.Of(kind);
        _fields.Add(field, new FieldAccessor(_offset, width, kind, 0));
        _offset += width;
        return this;
    }

    public RowLayoutBuilder AddIf(bool condition, string field, FieldKind kind = FieldKind.I32) =>
        condition ? Add(field, kind) : this;

    public RowLayout Build() => new(_name, _offset, _fields);
}
