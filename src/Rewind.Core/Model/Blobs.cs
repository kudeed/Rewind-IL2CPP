using System.Buffers.Binary;
using System.Text;
using Rewind.IO;
using Rewind.Metadata;
using Rewind.Runtime;

namespace Rewind.Model;

/// <summary>An enum constant: the enum type plus the boxed underlying integer.</summary>
public sealed record EnumConstant(TypeDef EnumType, object Value);

/// <summary>An array constant inside an attribute argument.</summary>
public sealed record ArrayConstant(Il2CppTypeEnum ElementType, TypeDef? ElementEnumType, object?[] Items);

/// <summary>A typeof(...) constant.</summary>
public sealed record TypeConstant(TypeSig Type);

public sealed class CustomAttribute
{
    public TypeDef AttributeType = null!;

    /// <summary>The constructor used; null for pre-v29 metadata, which records only the attribute type.</summary>
    public MethodDef? Constructor;

    public object?[] Arguments = [];
    public List<(FieldDef Field, object? Value)> Fields = [];
    public List<(PropertyDef Property, object? Value)> Properties = [];

    /// <summary>False when only the type is known (arguments live in native code before v29).</summary>
    public bool HasArguments;
}

/// <summary>Decodes constant blobs: field/parameter default values and v29+ custom attribute arguments.</summary>
public sealed class BlobDecoder(Il2CppModel model)
{
    private readonly bool _compressed = model.Version >= MetaVersion.V29_0;

    /// <summary>Default value of a field, or null (also returned for a genuine null default).</summary>
    public object? ReadFieldDefault(FieldDef field)
    {
        if (!field.HasDefault) return null;
        return ReadDefault(field.DefaultTypeIndex, field.DefaultDataIndex, field.Type);
    }

    public object? ReadParameterDefault(ParamDef parameter)
    {
        if (!parameter.HasDefault) return null;
        return ReadDefault(parameter.DefaultTypeIndex, parameter.DefaultDataIndex, parameter.Type);
    }

    private object? ReadDefault(int typeIndex, int dataIndex, TypeSig declared)
    {
        if (dataIndex < 0 || typeIndex < 0 || typeIndex >= model.Binary.Types.Count) return null;
        ReadOnlySpan<byte> data = model.Metadata.GetDefaultValueData(dataIndex);
        if (data.IsEmpty) return null;
        int pos = 0;
        object? value;
        try
        {
            value = ReadValue(model.Binary.Types[typeIndex].Type, data, ref pos);
        }
        catch (Exception e) when (e is IndexOutOfRangeException or ArgumentOutOfRangeException or InvalidDataException)
        {
            return null;
        }
        // Defaults are stored with the underlying integral type; re-attach the enum type for display.
        TypeSig target = declared is ByRefSig br ? br.ElementType : declared;
        if (value != null && target.Definition is { IsEnum: true } enumType && value is not string)
            return new EnumConstant(enumType, value);
        return value;
    }

    private (Il2CppTypeEnum Type, TypeDef? EnumType) ReadEncodedType(ReadOnlySpan<byte> data, ref int pos)
    {
        var type = (Il2CppTypeEnum)data[pos++];
        if (type != Il2CppTypeEnum.Enum) return (type, null);
        int enumTypeIndex = VarInt.ReadCompressedInt32(data, ref pos);
        TypeDef? enumType = model.TypeAt(enumTypeIndex)?.Definition;
        Il2CppTypeEnum underlying = enumType?.EnumUnderlyingType is PrimitiveSig p ? p.Element : Il2CppTypeEnum.I4;
        return (underlying, enumType);
    }

    private object? ReadValue(Il2CppTypeEnum type, ReadOnlySpan<byte> data, ref int pos)
    {
        switch (type)
        {
            case Il2CppTypeEnum.Boolean:
                return data[pos++] != 0;
            case Il2CppTypeEnum.U1:
                return data[pos++];
            case Il2CppTypeEnum.I1:
                return (sbyte)data[pos++];
            case Il2CppTypeEnum.Char:
            {
                char c = (char)BinaryPrimitives.ReadUInt16LittleEndian(data[pos..]);
                pos += 2;
                return c;
            }
            case Il2CppTypeEnum.U2:
            {
                ushort v = BinaryPrimitives.ReadUInt16LittleEndian(data[pos..]);
                pos += 2;
                return v;
            }
            case Il2CppTypeEnum.I2:
            {
                short v = BinaryPrimitives.ReadInt16LittleEndian(data[pos..]);
                pos += 2;
                return v;
            }
            case Il2CppTypeEnum.U4:
            {
                if (_compressed) return VarInt.ReadCompressedUInt32(data, ref pos);
                uint v = BinaryPrimitives.ReadUInt32LittleEndian(data[pos..]);
                pos += 4;
                return v;
            }
            case Il2CppTypeEnum.I4:
            {
                if (_compressed) return VarInt.ReadCompressedInt32(data, ref pos);
                int v = BinaryPrimitives.ReadInt32LittleEndian(data[pos..]);
                pos += 4;
                return v;
            }
            case Il2CppTypeEnum.U8:
            {
                ulong v = BinaryPrimitives.ReadUInt64LittleEndian(data[pos..]);
                pos += 8;
                return v;
            }
            case Il2CppTypeEnum.I8:
            {
                long v = BinaryPrimitives.ReadInt64LittleEndian(data[pos..]);
                pos += 8;
                return v;
            }
            case Il2CppTypeEnum.R4:
            {
                float v = BinaryPrimitives.ReadSingleLittleEndian(data[pos..]);
                pos += 4;
                return v;
            }
            case Il2CppTypeEnum.R8:
            {
                double v = BinaryPrimitives.ReadDoubleLittleEndian(data[pos..]);
                pos += 8;
                return v;
            }
            case Il2CppTypeEnum.I:
            case Il2CppTypeEnum.U:
            {
                // Only reachable for defaults of native-int constants; stored as 8 bytes.
                long v = BinaryPrimitives.ReadInt64LittleEndian(data[pos..]);
                pos += 8;
                return v;
            }
            case Il2CppTypeEnum.String:
            {
                int length;
                if (_compressed)
                {
                    length = VarInt.ReadCompressedInt32(data, ref pos);
                    if (length == -1) return null;
                }
                else
                {
                    length = BinaryPrimitives.ReadInt32LittleEndian(data[pos..]);
                    pos += 4;
                    if (length < 0) return null;
                }
                string s = Encoding.UTF8.GetString(data.Slice(pos, length));
                pos += length;
                return s;
            }
            case Il2CppTypeEnum.SzArray:
            {
                int length = VarInt.ReadCompressedInt32(data, ref pos);
                if (length == -1) return null;
                var (elementType, enumType) = ReadEncodedType(data, ref pos);
                bool different = data[pos++] == 1;
                var items = new object?[length];
                for (int i = 0; i < length; i++)
                {
                    Il2CppTypeEnum itemType = elementType;
                    TypeDef? itemEnum = enumType;
                    if (different) (itemType, itemEnum) = ReadEncodedType(data, ref pos);
                    object? item = ReadValue(itemType, data, ref pos);
                    items[i] = itemEnum != null && item != null ? new EnumConstant(itemEnum, item) : item;
                }
                return new ArrayConstant(elementType, enumType, items);
            }
            case Il2CppTypeEnum.Il2CppTypeIndex:
            {
                int typeIndex = VarInt.ReadCompressedInt32(data, ref pos);
                if (typeIndex == -1) return null;
                return model.TypeAt(typeIndex) is { } sig ? new TypeConstant(sig) : null;
            }
            case Il2CppTypeEnum.Class:
            case Il2CppTypeEnum.Object:
            case Il2CppTypeEnum.GenericInst:
                return null;
            default:
                throw new InvalidDataException($"Unsupported constant type {type}");
        }
    }

    private object? ReadAttributeValue(ReadOnlySpan<byte> data, ref int pos)
    {
        var (type, enumType) = ReadEncodedType(data, ref pos);
        object? value = ReadValue(type, data, ref pos);
        return enumType != null && value != null ? new EnumConstant(enumType, value) : value;
    }

    /// <summary>All custom attributes applied to the metadata token <paramref name="token"/> in one assembly.</summary>
    public List<CustomAttribute> ReadAttributes(AssemblyModel assembly, uint token, int legacyIndex = -1)
    {
        var result = new List<CustomAttribute>();
        MetadataFile md = model.Metadata;

        if (model.Version >= MetaVersion.V29_0)
        {
            int row = FindRange(md.AttributeDataRanges, assembly, token);
            if (row < 0) return result;
            ReadOnlySpan<byte> data = md.GetAttributeData(row);
            if (data.IsEmpty) return result;
            try
            {
                int pos = 0;
                int count = (int)VarInt.ReadCompressedUInt32(data, ref pos);
                if (count < 0 || count > 4096) return result;
                var ctors = new MethodDef?[count];
                for (int i = 0; i < count; i++)
                {
                    int ctorIndex = BinaryPrimitives.ReadInt32LittleEndian(data[pos..]);
                    pos += 4;
                    ctors[i] = ctorIndex >= 0 && ctorIndex < model.Methods.Length ? model.Methods[ctorIndex] : null;
                }
                for (int i = 0; i < count; i++)
                {
                    MethodDef? ctor = ctors[i];
                    int argCount = (int)VarInt.ReadCompressedUInt32(data, ref pos);
                    int fieldCount = (int)VarInt.ReadCompressedUInt32(data, ref pos);
                    int propertyCount = (int)VarInt.ReadCompressedUInt32(data, ref pos);
                    var attr = new CustomAttribute
                    {
                        Constructor = ctor,
                        AttributeType = ctor?.DeclaringType ?? model.Types[0],
                        Arguments = new object?[argCount],
                        HasArguments = true,
                    };
                    for (int a = 0; a < argCount; a++) attr.Arguments[a] = ReadAttributeValue(data, ref pos);
                    for (int f = 0; f < fieldCount; f++)
                    {
                        object? value = ReadAttributeValue(data, ref pos);
                        var (owner, index) = ReadMember(data, ref pos, attr.AttributeType);
                        if (owner != null && index >= 0 && index < owner.Fields.Length)
                            attr.Fields.Add((owner.Fields[index], value));
                    }
                    for (int p = 0; p < propertyCount; p++)
                    {
                        object? value = ReadAttributeValue(data, ref pos);
                        var (owner, index) = ReadMember(data, ref pos, attr.AttributeType);
                        if (owner != null && index >= 0 && index < owner.Properties.Length)
                            attr.Properties.Add((owner.Properties[index], value));
                    }
                    if (ctor != null) result.Add(attr);
                }
            }
            catch (Exception e) when (e is IndexOutOfRangeException or ArgumentOutOfRangeException or InvalidDataException)
            {
                // A malformed blob leaves the attributes decoded so far; better partial than none.
            }
            return result;
        }

        // Before v29 only the attribute types are in the metadata.
        int rangeIndex = legacyIndex;
        if (model.Version >= MetaVersion.V24_1)
            rangeIndex = FindLegacyRange(md.AttributeTypeRanges, assembly, token);
        if (rangeIndex < 0 || rangeIndex >= md.AttributeTypeRanges.Length) return result;
        AttributeTypeRangeRow range = md.AttributeTypeRanges[rangeIndex];
        for (int i = 0; i < range.Count; i++)
        {
            int slot = range.Start + i;
            if (slot < 0 || slot >= md.AttributeTypes.Length) break;
            if (model.TypeAt(md.AttributeTypes[slot])?.Definition is { } type)
                result.Add(new CustomAttribute { AttributeType = type });
        }
        return result;
    }

    private (TypeDef? Owner, int Index) ReadMember(ReadOnlySpan<byte> data, ref int pos, TypeDef attributeType)
    {
        int memberIndex = VarInt.ReadCompressedInt32(data, ref pos);
        if (memberIndex >= 0) return (attributeType, memberIndex);
        memberIndex = -(memberIndex + 1);
        int typeDefIndex = (int)VarInt.ReadCompressedUInt32(data, ref pos);
        TypeDef? owner = typeDefIndex >= 0 && typeDefIndex < model.Types.Length ? model.Types[typeDefIndex] : null;
        return (owner, memberIndex);
    }

    private static int FindRange(AttributeDataRangeRow[] ranges, AssemblyModel assembly, uint token)
    {
        int lo = assembly.CustomAttributeStart, hi = lo + assembly.CustomAttributeCount - 1;
        if (lo < 0) return -1;
        while (lo <= hi)
        {
            int mid = (lo + hi) >>> 1;
            if (mid >= ranges.Length) return -1;
            uint t = ranges[mid].Token;
            if (t == token) return mid;
            if (t < token) lo = mid + 1;
            else hi = mid - 1;
        }
        return -1;
    }

    private static int FindLegacyRange(AttributeTypeRangeRow[] ranges, AssemblyModel assembly, uint token)
    {
        int lo = assembly.CustomAttributeStart, hi = lo + assembly.CustomAttributeCount - 1;
        if (lo < 0) return -1;
        while (lo <= hi)
        {
            int mid = (lo + hi) >>> 1;
            if (mid >= ranges.Length) return -1;
            uint t = ranges[mid].Token;
            if (t == token) return mid;
            if (t < token) lo = mid + 1;
            else hi = mid - 1;
        }
        return -1;
    }
}
