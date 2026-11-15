using System.Buffers.Binary;
using System.Text;
using Rewind.IO;

namespace Rewind.Metadata;

public sealed class MetadataFormatException : Exception
{
    /// <summary>True when the file does not start with the IL2CPP magic at all (protected or not a metadata file).</summary>
    public bool NotStandardFormat { get; }

    public MetadataFormatException(string message, bool notStandardFormat = false) : base(message) =>
        NotStandardFormat = notStandardFormat;
}

/// <summary>
/// Parsed global-metadata.dat. Rows are normalized: fields that a given version lacks read as 0 or -1, and the
/// variable-width indexes of v38+ are widened to int.
/// </summary>
public sealed class MetadataFile
{
    public const uint Magic = 0xFAB11BAF;

    private readonly ByteBlock _data;
    private readonly Dictionary<string, MetaSection> _sections = new(StringComparer.Ordinal);
    private readonly Dictionary<int, string> _stringCache = [];
    private MetaSection _strings, _stringLiterals, _stringLiteralData, _defaultValueData, _attributeData;
    private int _stringLiteralRowSize;

    /// <summary>Version number stored in the file header.</summary>
    public int MajorVersion { get; }

    /// <summary>Exact layout version used for parsing (see <see cref="MetaVersion"/>).</summary>
    public int Version { get; internal set; }

    public IndexWidths Widths { get; private set; } = IndexWidths.Fixed;
    public int FileSize => _data.Length;

    public ImageRow[] Images = [];
    public AssemblyRow[] Assemblies = [];
    public TypeDefRow[] Types = [];
    public MethodDefRow[] Methods = [];
    public ParameterDefRow[] Parameters = [];
    public FieldDefRow[] Fields = [];
    public PropertyDefRow[] Properties = [];
    public EventDefRow[] Events = [];
    public GenericContainerRow[] GenericContainers = [];
    public GenericParameterRow[] GenericParameters = [];
    public InterfaceOffsetRow[] InterfaceOffsets = [];
    public FieldRefRow[] FieldRefs = [];
    public DefaultValueRow[] FieldDefaultValues = [];
    public DefaultValueRow[] ParameterDefaultValues = [];
    public int[] GenericParameterConstraints = [];
    public int[] NestedTypes = [];
    public int[] Interfaces = [];
    public uint[] VTableMethods = [];
    public int[] ReferencedAssemblies = [];
    public int[] ExportedTypes = [];

    public AttributeTypeRangeRow[] AttributeTypeRanges = [];
    public int[] AttributeTypes = [];
    public AttributeDataRangeRow[] AttributeDataRanges = [];
    public MetadataUsageListRow[] MetadataUsageLists = [];
    public MetadataUsagePairRow[] MetadataUsagePairs = [];
    public RgctxRow[] RgctxEntries = [];

    public int StringLiteralCount { get; private set; }

    public IReadOnlyDictionary<string, MetaSection> Sections => _sections;

    private MetadataFile(byte[] data, int major, int version)
    {
        _data = new ByteBlock(data);
        MajorVersion = major;
        Version = version;
    }

    public static bool HasMagic(ReadOnlySpan<byte> data) =>
        data.Length >= 8 && BinaryPrimitives.ReadUInt32LittleEndian(data) == Magic;

    public static int ReadMajorVersion(ReadOnlySpan<byte> data) => BinaryPrimitives.ReadInt32LittleEndian(data[4..]);

    /// <summary>The header's section names, in file order, for one layout version.</summary>
    private static List<string> HeaderSectionNames(int v)
    {
        var names = new List<string>
        {
            "stringLiterals", "stringLiteralData", "strings", "events", "properties", "methods",
            "parameterDefaultValues", "fieldDefaultValues", "fieldAndParameterDefaultValueData",
            "fieldMarshaledSizes", "parameters", "fields", "genericParameters", "genericParameterConstraints",
            "genericContainers", "nestedTypes", "interfaces", "vtableMethods", "interfaceOffsets", "typeDefinitions",
        };
        if (v <= MetaVersion.V24_15) names.Add("rgctxEntries");
        names.Add("images");
        names.Add("assemblies");
        if (v < MetaVersion.V27_0)
        {
            names.Add("metadataUsageLists");
            names.Add("metadataUsagePairs");
        }
        names.Add("fieldRefs");
        names.Add("referencedAssemblies");
        if (v < MetaVersion.V29_0)
        {
            names.Add("attributesInfo");
            names.Add("attributeTypes");
        }
        else
        {
            names.Add("attributeData");
            names.Add("attributeDataRanges");
        }
        names.Add("unresolvedVirtualCallParameterTypes");
        names.Add("unresolvedVirtualCallParameterRanges");
        names.Add("windowsRuntimeTypeNames");
        if (v >= MetaVersion.V27_0) names.Add("windowsRuntimeStrings");
        names.Add("exportedTypeDefinitions");
        return names;
    }

    /// <summary>
    /// Parses the file with one specific layout version. Throws <see cref="MetadataFormatException"/> when the
    /// data is not consistent with that layout, which is how callers probe sub-versions.
    /// </summary>
    public static MetadataFile Parse(byte[] data, int version)
    {
        if (!HasMagic(data))
            throw new MetadataFormatException(
                "The metadata file does not start with the IL2CPP signature (0xFAB11BAF). It is either not a " +
                "global-metadata.dat file or it has been encrypted/obfuscated by the game's protection.",
                notStandardFormat: true);

        int major = ReadMajorVersion(data);
        if (version / 100 != major)
            throw new MetadataFormatException($"Layout {MetaVersion.Describe(version)} does not match file version {major}");

        var file = new MetadataFile(data, major, version);
        file.ReadHeader();
        file.ReadTables();
        file.Validate();
        return file;
    }

    private MetaSection Section(string name) => _sections.TryGetValue(name, out MetaSection s) ? s : default;

    private void ReadHeader()
    {
        List<string> names = HeaderSectionNames(Version);
        bool withCounts = Version >= MetaVersion.V38;
        int entrySize = withCounts ? 12 : 8;
        int headerSize = 8 + names.Count * entrySize;
        if (_data.Length < headerSize) throw new MetadataFormatException("Metadata file is shorter than its header");

        for (int i = 0; i < names.Count; i++)
        {
            int p = 8 + i * entrySize;
            int offset = _data.I32(p);
            int size = _data.I32(p + 4);
            int count = withCounts ? _data.I32(p + 8) : -1;
            if (offset < 0 || size < 0 || (long)offset + size > _data.Length)
                throw new MetadataFormatException($"Section '{names[i]}' lies outside the file (layout {MetaVersion.Describe(Version)})");
            _sections[names[i]] = new MetaSection(offset, size, count);
        }

        // libil2cpp asserts that the first section starts right after the header; this pins the header shape.
        if (_sections["stringLiterals"].Offset != headerSize)
            throw new MetadataFormatException(
                $"Header size mismatch for layout {MetaVersion.Describe(Version)}: expected first section at {headerSize}, found {_sections["stringLiterals"].Offset}");

        _strings = Section("strings");
        _stringLiterals = Section("stringLiterals");
        _stringLiteralData = Section("stringLiteralData");
        _defaultValueData = Section("fieldAndParameterDefaultValueData");
        _attributeData = Section("attributeData");
    }

    private IndexWidths DetermineWidths()
    {
        if (Version < MetaVersion.V38) return IndexWidths.Fixed;

        int typeDef = IndexWidths.ForCount(Section("typeDefinitions").Count);
        int container = IndexWidths.ForCount(Section("genericContainers").Count);
        int parameter = Version >= MetaVersion.V39 ? IndexWidths.ForCount(Section("parameters").Count) : 4;

        // The Il2CppType table lives in the binary, so its index width is inferred from a row that holds exactly
        // one type index plus fixed-size fields.
        int type = 4;
        MetaSection io = Section("interfaceOffsets");
        MetaSection fields = Section("fields");
        MetaSection itf = Section("interfaces");
        if (io.Count > 0) type = io.Size / io.Count - 4;
        else if (fields.Count > 0) type = fields.Size / fields.Count - 8;
        else if (itf.Count > 0) type = itf.Size / itf.Count;
        if (type is not (1 or 2 or 4))
            throw new MetadataFormatException($"Could not infer the type index width (got {type})");
        return new IndexWidths(type, typeDef, container, parameter);
    }

    private RowLayoutBuilder Layout(string name) => new(name, Version, Widths);

    private delegate T RowReader<out T>(ReadOnlySpan<byte> row);

    private T[] ReadRows<T>(string section, RowLayout layout, RowReader<T> read)
    {
        MetaSection s = Section(section);
        if (s.Size == 0) return [];
        if (layout.Size == 0 || s.Size % layout.Size != 0)
            throw new MetadataFormatException(
                $"Section '{section}' ({s.Size} bytes) is not a whole number of {layout.Size}-byte rows (layout {MetaVersion.Describe(Version)})");
        int count = s.Size / layout.Size;
        if (s.Count >= 0 && s.Count != count)
            throw new MetadataFormatException(
                $"Section '{section}' declares {s.Count} rows but holds {count} (layout {MetaVersion.Describe(Version)})");
        var rows = new T[count];
        ReadOnlySpan<byte> all = _data.Span(s.Offset, s.Size);
        for (int i = 0; i < count; i++)
            rows[i] = read(all.Slice(i * layout.Size, layout.Size));
        return rows;
    }

    private int[] ReadIndexArray(string section, int width)
    {
        MetaSection s = Section(section);
        if (s.Size == 0) return [];
        if (s.Size % width != 0)
            throw new MetadataFormatException($"Section '{section}' is not a whole number of {width}-byte indexes");
        int count = s.Size / width;
        var result = new int[count];
        ReadOnlySpan<byte> all = _data.Span(s.Offset, s.Size);
        for (int i = 0; i < count; i++)
        {
            if (width == 1)
            {
                result[i] = all[i] == byte.MaxValue ? -1 : all[i];
            }
            else if (width == 2)
            {
                ushort value = BinaryPrimitives.ReadUInt16LittleEndian(all[(i * 2)..]);
                result[i] = value == ushort.MaxValue ? -1 : value;
            }
            else
            {
                result[i] = BinaryPrimitives.ReadInt32LittleEndian(all[(i * 4)..]);
            }
        }
        return result;
    }

    private void ReadTables()
    {
        int v = Version;
        Widths = DetermineWidths();

        // ---- type definitions
        RowLayout lt = Layout("Il2CppTypeDefinition")
            .Add("nameIndex").Add("namespaceIndex")
            .Add("customAttributeIndex", max: MetaVersion.V24_0)
            .Add("byvalTypeIndex", FieldKind.TypeIndex)
            .Add("byrefTypeIndex", max: MetaVersion.V24_5)
            .Add("declaringTypeIndex", FieldKind.TypeIndex)
            .Add("parentIndex", FieldKind.TypeIndex)
            .Add("elementTypeIndex", max: MetaVersion.V35 - 1)
            .Add("rgctxStartIndex", max: MetaVersion.V24_15)
            .Add("rgctxCount", max: MetaVersion.V24_15)
            .Add("genericContainerIndex", FieldKind.GenericContainerIndex)
            .Add("flags", FieldKind.U32)
            .Add("fieldStart").Add("methodStart").Add("eventStart").Add("propertyStart")
            .Add("nestedTypesStart").Add("interfacesStart").Add("vtableStart").Add("interfaceOffsetsStart")
            .Add("method_count", FieldKind.U16).Add("property_count", FieldKind.U16)
            .Add("field_count", FieldKind.U16).Add("event_count", FieldKind.U16)
            .Add("nested_type_count", FieldKind.U16).Add("vtable_count", FieldKind.U16)
            .Add("interfaces_count", FieldKind.U16).Add("interface_offsets_count", FieldKind.U16)
            .Add("bitfield", FieldKind.U32).Add("token", FieldKind.U32)
            .Build();
        {
            FieldAccessor name = lt.Field("nameIndex"), ns = lt.Field("namespaceIndex"),
                ca = lt.Field("customAttributeIndex", -1), byval = lt.Field("byvalTypeIndex"),
                decl = lt.Field("declaringTypeIndex"), parent = lt.Field("parentIndex"),
                elem = lt.Field("elementTypeIndex", -1), rs = lt.Field("rgctxStartIndex", -1),
                rc = lt.Field("rgctxCount"), gc = lt.Field("genericContainerIndex"), flags = lt.Field("flags"),
                fs = lt.Field("fieldStart"), ms = lt.Field("methodStart"), es = lt.Field("eventStart"),
                ps = lt.Field("propertyStart"), nts = lt.Field("nestedTypesStart"), ifs = lt.Field("interfacesStart"),
                vs = lt.Field("vtableStart"), ios = lt.Field("interfaceOffsetsStart"),
                mc = lt.Field("method_count"), pc = lt.Field("property_count"), fc = lt.Field("field_count"),
                ec = lt.Field("event_count"), ntc = lt.Field("nested_type_count"), vc = lt.Field("vtable_count"),
                ic = lt.Field("interfaces_count"), ioc = lt.Field("interface_offsets_count"),
                bits = lt.Field("bitfield"), token = lt.Field("token");
            Types = ReadRows("typeDefinitions", lt, r => new TypeDefRow
            {
                NameIndex = name.Int(r), NamespaceIndex = ns.Int(r), CustomAttributeIndex = ca.Int(r),
                ByvalTypeIndex = byval.Int(r), DeclaringTypeIndex = decl.Int(r), ParentIndex = parent.Int(r),
                ElementTypeIndex = elem.Int(r), RgctxStartIndex = rs.Int(r), RgctxCount = rc.Int(r),
                GenericContainerIndex = gc.Int(r), Flags = flags.UInt(r),
                FieldStart = fs.Int(r), MethodStart = ms.Int(r), EventStart = es.Int(r), PropertyStart = ps.Int(r),
                NestedTypesStart = nts.Int(r), InterfacesStart = ifs.Int(r), VtableStart = vs.Int(r),
                InterfaceOffsetsStart = ios.Int(r),
                MethodCount = mc.UShort(r), PropertyCount = pc.UShort(r), FieldCount = fc.UShort(r),
                EventCount = ec.UShort(r), NestedTypeCount = ntc.UShort(r), VtableCount = vc.UShort(r),
                InterfacesCount = ic.UShort(r), InterfaceOffsetsCount = ioc.UShort(r),
                Bitfield = bits.UInt(r), Token = token.UInt(r),
            });
        }

        // ---- methods
        RowLayout lm = Layout("Il2CppMethodDefinition")
            .Add("nameIndex")
            .Add("declaringType", FieldKind.TypeDefIndex)
            .Add("returnType", FieldKind.TypeIndex)
            .Add("returnParameterToken", FieldKind.U32, min: MetaVersion.V31_0)
            .Add("parameterStart", FieldKind.ParameterIndex)
            .Add("customAttributeIndex", max: MetaVersion.V24_0)
            .Add("genericContainerIndex", FieldKind.GenericContainerIndex)
            .Add("methodIndex", max: MetaVersion.V24_15)
            .Add("invokerIndex", max: MetaVersion.V24_15)
            .Add("delegateWrapperIndex", max: MetaVersion.V24_15)
            .Add("rgctxStartIndex", max: MetaVersion.V24_15)
            .Add("rgctxCount", max: MetaVersion.V24_15)
            .Add("token", FieldKind.U32)
            .Add("flags", FieldKind.U16).Add("iflags", FieldKind.U16)
            .Add("slot", FieldKind.U16).Add("parameterCount", FieldKind.U16)
            .Build();
        {
            FieldAccessor name = lm.Field("nameIndex"), decl = lm.Field("declaringType"), ret = lm.Field("returnType"),
                rpt = lm.Field("returnParameterToken"), ps = lm.Field("parameterStart"),
                ca = lm.Field("customAttributeIndex", -1), gc = lm.Field("genericContainerIndex"),
                mi = lm.Field("methodIndex", -1), ii = lm.Field("invokerIndex", -1),
                dw = lm.Field("delegateWrapperIndex", -1), rs = lm.Field("rgctxStartIndex", -1),
                rc = lm.Field("rgctxCount"), token = lm.Field("token"), flags = lm.Field("flags"),
                iflags = lm.Field("iflags"), slot = lm.Field("slot"), pcount = lm.Field("parameterCount");
            Methods = ReadRows("methods", lm, r => new MethodDefRow
            {
                NameIndex = name.Int(r), DeclaringType = decl.Int(r), ReturnType = ret.Int(r),
                ReturnParameterToken = rpt.UInt(r), ParameterStart = ps.Int(r), CustomAttributeIndex = ca.Int(r),
                GenericContainerIndex = gc.Int(r), MethodIndex = mi.Int(r), InvokerIndex = ii.Int(r),
                DelegateWrapperIndex = dw.Int(r), RgctxStartIndex = rs.Int(r), RgctxCount = rc.Int(r),
                Token = token.UInt(r), Flags = flags.UShort(r), ImplFlags = iflags.UShort(r),
                Slot = slot.UShort(r), ParameterCount = pcount.UShort(r),
            });
        }

        // ---- parameters
        RowLayout lp = Layout("Il2CppParameterDefinition")
            .Add("nameIndex").Add("token", FieldKind.U32)
            .Add("customAttributeIndex", max: MetaVersion.V24_0)
            .Add("typeIndex", FieldKind.TypeIndex).Build();
        {
            FieldAccessor name = lp.Field("nameIndex"), token = lp.Field("token"),
                ca = lp.Field("customAttributeIndex", -1), type = lp.Field("typeIndex");
            Parameters = ReadRows("parameters", lp, r => new ParameterDefRow
            {
                NameIndex = name.Int(r), Token = token.UInt(r), CustomAttributeIndex = ca.Int(r), TypeIndex = type.Int(r),
            });
        }

        // ---- fields
        RowLayout lf = Layout("Il2CppFieldDefinition")
            .Add("nameIndex").Add("typeIndex", FieldKind.TypeIndex)
            .Add("customAttributeIndex", max: MetaVersion.V24_0)
            .Add("token", FieldKind.U32).Build();
        {
            FieldAccessor name = lf.Field("nameIndex"), type = lf.Field("typeIndex"),
                ca = lf.Field("customAttributeIndex", -1), token = lf.Field("token");
            Fields = ReadRows("fields", lf, r => new FieldDefRow
            {
                NameIndex = name.Int(r), TypeIndex = type.Int(r), CustomAttributeIndex = ca.Int(r), Token = token.UInt(r),
            });
        }

        // ---- properties
        RowLayout lpr = Layout("Il2CppPropertyDefinition")
            .Add("nameIndex").Add("get").Add("set").Add("attrs", FieldKind.U32)
            .Add("customAttributeIndex", max: MetaVersion.V24_0)
            .Add("token", FieldKind.U32).Build();
        {
            FieldAccessor name = lpr.Field("nameIndex"), get = lpr.Field("get"), set = lpr.Field("set"),
                attrs = lpr.Field("attrs"), ca = lpr.Field("customAttributeIndex", -1), token = lpr.Field("token");
            Properties = ReadRows("properties", lpr, r => new PropertyDefRow
            {
                NameIndex = name.Int(r), Get = get.Int(r), Set = set.Int(r), Attrs = attrs.UInt(r),
                CustomAttributeIndex = ca.Int(r), Token = token.UInt(r),
            });
        }

        // ---- events
        RowLayout le = Layout("Il2CppEventDefinition")
            .Add("nameIndex").Add("typeIndex", FieldKind.TypeIndex).Add("add").Add("remove").Add("raise")
            .Add("customAttributeIndex", max: MetaVersion.V24_0)
            .Add("token", FieldKind.U32).Build();
        {
            FieldAccessor name = le.Field("nameIndex"), type = le.Field("typeIndex"), add = le.Field("add"),
                remove = le.Field("remove"), raise = le.Field("raise"), ca = le.Field("customAttributeIndex", -1),
                token = le.Field("token");
            Events = ReadRows("events", le, r => new EventDefRow
            {
                NameIndex = name.Int(r), TypeIndex = type.Int(r), Add = add.Int(r), Remove = remove.Int(r),
                Raise = raise.Int(r), CustomAttributeIndex = ca.Int(r), Token = token.UInt(r),
            });
        }

        // ---- generics
        RowLayout lgc = Layout("Il2CppGenericContainer")
            .Add("ownerIndex").Add("type_argc").Add("is_method").Add("genericParameterStart").Build();
        {
            FieldAccessor owner = lgc.Field("ownerIndex"), argc = lgc.Field("type_argc"),
                isMethod = lgc.Field("is_method"), start = lgc.Field("genericParameterStart");
            GenericContainers = ReadRows("genericContainers", lgc, r => new GenericContainerRow
            {
                OwnerIndex = owner.Int(r), TypeArgc = argc.Int(r), IsMethod = isMethod.Int(r),
                GenericParameterStart = start.Int(r),
            });
        }

        RowLayout lgp = Layout("Il2CppGenericParameter")
            .Add("ownerIndex", FieldKind.GenericContainerIndex).Add("nameIndex")
            .Add("constraintsStart", FieldKind.I16).Add("constraintsCount", FieldKind.I16)
            .Add("num", FieldKind.U16).Add("flags", FieldKind.U16).Build();
        {
            FieldAccessor owner = lgp.Field("ownerIndex"), name = lgp.Field("nameIndex"),
                cs = lgp.Field("constraintsStart"), cc = lgp.Field("constraintsCount"), num = lgp.Field("num"),
                flags = lgp.Field("flags");
            GenericParameters = ReadRows("genericParameters", lgp, r => new GenericParameterRow
            {
                OwnerIndex = owner.Int(r), NameIndex = name.Int(r), ConstraintsStart = (short)cs.Int(r),
                ConstraintsCount = (short)cc.Int(r), Num = num.UShort(r), Flags = flags.UShort(r),
            });
        }

        // ---- small pair tables
        RowLayout lio = Layout("Il2CppInterfaceOffsetPair").Add("interfaceTypeIndex", FieldKind.TypeIndex).Add("offset").Build();
        {
            FieldAccessor type = lio.Field("interfaceTypeIndex"), offset = lio.Field("offset");
            InterfaceOffsets = ReadRows("interfaceOffsets", lio, r => new InterfaceOffsetRow
            {
                InterfaceTypeIndex = type.Int(r), Offset = offset.Int(r),
            });
        }

        RowLayout lfr = Layout("Il2CppFieldRef").Add("typeIndex", FieldKind.TypeIndex).Add("fieldIndex").Build();
        {
            FieldAccessor type = lfr.Field("typeIndex"), field = lfr.Field("fieldIndex");
            FieldRefs = ReadRows("fieldRefs", lfr, r => new FieldRefRow { TypeIndex = type.Int(r), FieldIndex = field.Int(r) });
        }

        RowLayout lfd = Layout("Il2CppFieldDefaultValue").Add("fieldIndex").Add("typeIndex", FieldKind.TypeIndex).Add("dataIndex").Build();
        {
            FieldAccessor owner = lfd.Field("fieldIndex"), type = lfd.Field("typeIndex"), data = lfd.Field("dataIndex");
            FieldDefaultValues = ReadRows("fieldDefaultValues", lfd, r => new DefaultValueRow
            {
                OwnerIndex = owner.Int(r), TypeIndex = type.Int(r), DataIndex = data.Int(r),
            });
        }

        RowLayout lpd = Layout("Il2CppParameterDefaultValue")
            .Add("parameterIndex", FieldKind.ParameterIndex).Add("typeIndex", FieldKind.TypeIndex).Add("dataIndex").Build();
        {
            FieldAccessor owner = lpd.Field("parameterIndex"), type = lpd.Field("typeIndex"), data = lpd.Field("dataIndex");
            ParameterDefaultValues = ReadRows("parameterDefaultValues", lpd, r => new DefaultValueRow
            {
                OwnerIndex = owner.Int(r), TypeIndex = type.Int(r), DataIndex = data.Int(r),
            });
        }

        // ---- images and assemblies
        RowLayout li = Layout("Il2CppImageDefinition")
            .Add("nameIndex").Add("assemblyIndex")
            .Add("typeStart", FieldKind.TypeDefIndex).Add("typeCount", FieldKind.U32)
            .Add("exportedTypeStart", FieldKind.TypeDefIndex).Add("exportedTypeCount", FieldKind.U32)
            .Add("entryPointIndex").Add("token", FieldKind.U32)
            .Add("customAttributeStart", min: MetaVersion.V24_1)
            .Add("customAttributeCount", FieldKind.U32, min: MetaVersion.V24_1)
            .Build();
        {
            FieldAccessor name = li.Field("nameIndex"), asm = li.Field("assemblyIndex"), ts = li.Field("typeStart"),
                tc = li.Field("typeCount"), ets = li.Field("exportedTypeStart"), etc = li.Field("exportedTypeCount"),
                ep = li.Field("entryPointIndex"), token = li.Field("token"),
                cas = li.Field("customAttributeStart", -1), cac = li.Field("customAttributeCount");
            Images = ReadRows("images", li, r => new ImageRow
            {
                NameIndex = name.Int(r), AssemblyIndex = asm.Int(r), TypeStart = ts.Int(r), TypeCount = tc.UInt(r),
                ExportedTypeStart = ets.Int(r), ExportedTypeCount = etc.UInt(r), EntryPointIndex = ep.Int(r),
                Token = token.UInt(r), CustomAttributeStart = cas.Int(r), CustomAttributeCount = cac.UInt(r),
                Name = "",
            });
        }

        // hashValueIndex existed up to 24.3 except in the 2018.4.34+ branch (24.15).
        bool hasHashValue = v <= MetaVersion.V24_3 && v != MetaVersion.V24_15;
        RowLayout la = Layout("Il2CppAssemblyDefinition")
            .Add("imageIndex")
            .Add("token", FieldKind.U32, min: MetaVersion.V24_1)
            .Add("moduleToken", FieldKind.U32, min: MetaVersion.V38)
            .Add("customAttributeIndex", max: MetaVersion.V24_0)
            .Add("referencedAssemblyStart").Add("referencedAssemblyCount")
            .Add("nameIndex").Add("cultureIndex")
            .AddIf(hasHashValue, "hashValueIndex")
            .Add("publicKeyIndex").Add("hash_alg", FieldKind.U32).Add("hash_len").Add("flags", FieldKind.U32)
            .Add("major").Add("minor").Add("build").Add("revision")
            .Add("public_key_token", FieldKind.Bytes8)
            .Build();
        {
            FieldAccessor image = la.Field("imageIndex"), token = la.Field("token"), mtoken = la.Field("moduleToken"),
                ras = la.Field("referencedAssemblyStart"), rac = la.Field("referencedAssemblyCount"),
                name = la.Field("nameIndex"), culture = la.Field("cultureIndex"), pk = la.Field("publicKeyIndex"),
                alg = la.Field("hash_alg"), len = la.Field("hash_len"), flags = la.Field("flags"),
                major = la.Field("major"), minor = la.Field("minor"), build = la.Field("build"),
                rev = la.Field("revision"), pkt = la.Field("public_key_token");
            Assemblies = ReadRows("assemblies", la, r => new AssemblyRow
            {
                ImageIndex = image.Int(r), Token = token.UInt(r), ModuleToken = mtoken.UInt(r),
                ReferencedAssemblyStart = ras.Int(r), ReferencedAssemblyCount = rac.Int(r),
                NameIndex = name.Int(r), CultureIndex = culture.Int(r), PublicKeyIndex = pk.Int(r),
                HashAlg = alg.UInt(r), HashLen = len.Int(r), Flags = flags.UInt(r),
                Major = major.Int(r), Minor = minor.Int(r), Build = build.Int(r), Revision = rev.Int(r),
                PublicKeyToken = BinaryPrimitives.ReadUInt64LittleEndian(r.Slice(pkt.Offset, 8)),
                Name = "",
            });
        }

        // ---- plain index arrays
        GenericParameterConstraints = ReadIndexArray("genericParameterConstraints", Widths.Type);
        Interfaces = ReadIndexArray("interfaces", Widths.Type);
        NestedTypes = ReadIndexArray("nestedTypes", 4);
        ReferencedAssemblies = ReadIndexArray("referencedAssemblies", 4);
        ExportedTypes = ReadIndexArray("exportedTypeDefinitions", 4);
        int[] vtable = ReadIndexArray("vtableMethods", 4);
        VTableMethods = new uint[vtable.Length];
        for (int i = 0; i < vtable.Length; i++) VTableMethods[i] = (uint)vtable[i];

        // ---- string literals: v35 dropped the length; it is the distance to the next entry.
        _stringLiteralRowSize = v < MetaVersion.V35 ? 8 : 4;
        if (_stringLiterals.Size % _stringLiteralRowSize != 0)
            throw new MetadataFormatException("String literal table has a partial row");
        int literalRows = _stringLiterals.Size / _stringLiteralRowSize;
        StringLiteralCount = v < MetaVersion.V35 ? literalRows : Math.Max(0, literalRows - 1);

        // ---- attributes
        if (v < MetaVersion.V29_0)
        {
            RowLayout lar = Layout("Il2CppCustomAttributeTypeRange")
                .Add("token", FieldKind.U32, min: MetaVersion.V24_1).Add("start").Add("count").Build();
            FieldAccessor token = lar.Field("token"), start = lar.Field("start"), count = lar.Field("count");
            AttributeTypeRanges = ReadRows("attributesInfo", lar, r => new AttributeTypeRangeRow
            {
                Token = token.UInt(r), Start = start.Int(r), Count = count.Int(r),
            });
            AttributeTypes = ReadIndexArray("attributeTypes", 4);
        }
        else
        {
            RowLayout lad = Layout("Il2CppCustomAttributeDataRange")
                .Add("token", FieldKind.U32).Add("startOffset", FieldKind.U32).Build();
            FieldAccessor token = lad.Field("token"), start = lad.Field("startOffset");
            AttributeDataRanges = ReadRows("attributeDataRanges", lad, r => new AttributeDataRangeRow
            {
                Token = token.UInt(r), StartOffset = start.UInt(r),
            });
        }

        // ---- pre-v27 metadata usages, pre-24.2 rgctx
        if (v < MetaVersion.V27_0)
        {
            RowLayout ll = Layout("Il2CppMetadataUsageList").Add("start", FieldKind.U32).Add("count", FieldKind.U32).Build();
            FieldAccessor start = ll.Field("start"), count = ll.Field("count");
            MetadataUsageLists = ReadRows("metadataUsageLists", ll, r => new MetadataUsageListRow
            {
                Start = start.UInt(r), Count = count.UInt(r),
            });
            RowLayout lu = Layout("Il2CppMetadataUsagePair")
                .Add("destinationIndex", FieldKind.U32).Add("encodedSourceIndex", FieldKind.U32).Build();
            FieldAccessor dest = lu.Field("destinationIndex"), src = lu.Field("encodedSourceIndex");
            MetadataUsagePairs = ReadRows("metadataUsagePairs", lu, r => new MetadataUsagePairRow
            {
                DestinationIndex = dest.UInt(r), EncodedSourceIndex = src.UInt(r),
            });
        }
        if (v <= MetaVersion.V24_15)
        {
            RowLayout lr = Layout("Il2CppRGCTXDefinition").Add("type").Add("data").Build();
            FieldAccessor type = lr.Field("type"), data = lr.Field("data");
            RgctxEntries = ReadRows("rgctxEntries", lr, r => new RgctxRow { Type = type.Int(r), Data = data.Int(r) });
        }
    }

    /// <summary>Cross-checks row contents so that a wrong layout guess is rejected instead of yielding garbage.</summary>
    private void Validate()
    {
        string L = MetaVersion.Describe(Version);
        if (Images.Length == 0 || Types.Length == 0)
            throw new MetadataFormatException($"No images or types found (layout {L})");

        for (int i = 0; i < Images.Length; i++)
        {
            ref ImageRow im = ref Images[i];
            string? name = TryGetString(im.NameIndex);
            if (string.IsNullOrEmpty(name) || name.Length > 260 || HasControlChars(name))
                throw new MetadataFormatException($"Image {i} has an invalid name (layout {L})");
            im.Name = name;
            if (im.TypeStart < 0 || (long)im.TypeStart + im.TypeCount > Types.Length)
                throw new MetadataFormatException($"Image '{name}' type range is out of bounds (layout {L})");
        }

        for (int i = 0; i < Assemblies.Length; i++)
        {
            ref AssemblyRow a = ref Assemblies[i];
            string? name = TryGetString(a.NameIndex);
            if (name == null || name.Length > 260 || HasControlChars(name) ||
                a.ImageIndex < 0 || a.ImageIndex >= Images.Length)
                throw new MetadataFormatException($"Assembly {i} is invalid (layout {L})");
            a.Name = name;
        }

        // Sampling every row would be cheap too, but a stride keeps very large games fast.
        int step = Math.Max(1, Types.Length / 4096);
        for (int i = 0; i < Types.Length; i += step)
        {
            ref readonly TypeDefRow t = ref Types[i];
            if (TryGetString(t.NameIndex) == null || TryGetString(t.NamespaceIndex) == null)
                throw new MetadataFormatException($"Type {i} has an invalid name index (layout {L})");
            if (t.FieldCount != 0 && (t.FieldStart < 0 || t.FieldStart + t.FieldCount > Fields.Length))
                throw new MetadataFormatException($"Type {i} field range is out of bounds (layout {L})");
            if (t.MethodCount != 0 && (t.MethodStart < 0 || t.MethodStart + t.MethodCount > Methods.Length))
                throw new MetadataFormatException($"Type {i} method range is out of bounds (layout {L})");
            if (t.GenericContainerIndex < -1 || t.GenericContainerIndex >= GenericContainers.Length)
                throw new MetadataFormatException($"Type {i} generic container is out of bounds (layout {L})");
        }

        step = Math.Max(1, Methods.Length / 8192);
        for (int i = 0; i < Methods.Length; i += step)
        {
            ref readonly MethodDefRow m = ref Methods[i];
            if (TryGetString(m.NameIndex) == null || m.DeclaringType < 0 || m.DeclaringType >= Types.Length)
                throw new MetadataFormatException($"Method {i} is invalid (layout {L})");
            if (m.ParameterCount != 0 &&
                (m.ParameterStart < 0 || m.ParameterStart + m.ParameterCount > Parameters.Length))
                throw new MetadataFormatException($"Method {i} parameter range is out of bounds (layout {L})");
            if ((m.Token >> 24) != 0x06)
                throw new MetadataFormatException($"Method {i} token 0x{m.Token:X8} is not a MethodDef token (layout {L})");
        }
    }

    private static bool HasControlChars(string s)
    {
        foreach (char c in s)
            if (c < 0x20)
                return true;
        return false;
    }

    // ---- strings ---------------------------------------------------------------------------------------------

    private string? TryGetString(int index)
    {
        if (index < 0 || index >= _strings.Size) return null;
        return GetString(index);
    }

    /// <summary>A metadata (identifier) string by its byte offset into the string heap.</summary>
    public string GetString(int index)
    {
        if (_stringCache.TryGetValue(index, out string? cached)) return cached;
        if (index < 0 || index >= _strings.Size) return "";
        int start = _strings.Offset + index;
        int limit = _strings.Offset + _strings.Size;
        int end = Array.IndexOf(_data.Data, (byte)0, start, limit - start);
        if (end < 0) end = limit;
        string s = Encoding.UTF8.GetString(_data.Data, start, end - start);
        _stringCache[index] = s;
        return s;
    }

    /// <summary>Raw UTF-8 bytes of a managed string literal (what ldstr loads).</summary>
    public ReadOnlySpan<byte> GetStringLiteralBytes(int index)
    {
        if (index < 0 || index >= StringLiteralCount) return default;
        int row = _stringLiterals.Offset + index * _stringLiteralRowSize;
        int length, dataIndex;
        if (_stringLiteralRowSize == 8)
        {
            length = _data.I32(row);
            dataIndex = _data.I32(row + 4);
        }
        else
        {
            dataIndex = _data.I32(row);
            length = _data.I32(row + 4) - dataIndex;
        }
        if (length < 0 || dataIndex < 0 || (long)dataIndex + length > _stringLiteralData.Size) return default;
        return _data.Span(_stringLiteralData.Offset + dataIndex, length);
    }

    public string GetStringLiteral(int index) => Encoding.UTF8.GetString(GetStringLiteralBytes(index));

    /// <summary>Default value blob bytes starting at <paramref name="dataIndex"/> (runs to the end of the heap).</summary>
    public ReadOnlySpan<byte> GetDefaultValueData(int dataIndex)
    {
        if (dataIndex < 0 || dataIndex >= _defaultValueData.Size) return default;
        return _data.Span(_defaultValueData.Offset + dataIndex, _defaultValueData.Size - dataIndex);
    }

    /// <summary>v29+: serialized attribute data for one range row (bounded by the next row's start).</summary>
    public ReadOnlySpan<byte> GetAttributeData(int rangeIndex)
    {
        if (rangeIndex < 0 || rangeIndex + 1 >= AttributeDataRanges.Length) return default;
        uint start = AttributeDataRanges[rangeIndex].StartOffset;
        uint end = AttributeDataRanges[rangeIndex + 1].StartOffset;
        if (end < start || end > (uint)_attributeData.Size) return default;
        return _data.Span(_attributeData.Offset + (int)start, (int)(end - start));
    }

    public ReadOnlySpan<byte> SectionBytes(string name)
    {
        MetaSection s = Section(name);
        return s.Size == 0 ? default : _data.Span(s.Offset, s.Size);
    }
}
