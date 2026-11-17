using Rewind.Binary;
using Rewind.Metadata;
using Rewind.Runtime;

namespace Rewind.Model;

public enum UsageKind { Invalid = 0, TypeInfo = 1, Il2CppType = 2, MethodDef = 3, FieldInfo = 4, StringLiteral = 5, MethodRef = 6, FieldRva = 7 }

/// <summary>What a metadata usage slot (a global the generated code reads) stands for.</summary>
public sealed record MetadataUsage(UsageKind Kind, int Index)
{
    public TypeSig? Type { get; init; }
    public MethodDef? Method { get; init; }
    public MethodInst? MethodInst { get; init; }
    public FieldDef? Field { get; init; }
    public string? String { get; init; }

    public override string ToString() => Kind switch
    {
        UsageKind.TypeInfo => $"class {Type}",
        UsageKind.Il2CppType => $"typeof {Type}",
        UsageKind.MethodDef => $"method {Method}",
        UsageKind.MethodRef => $"method {MethodInst}",
        UsageKind.FieldInfo => $"field {Field}",
        UsageKind.FieldRva => $"field-data {Field}",
        UsageKind.StringLiteral => $"string \"{String}\"",
        _ => "invalid",
    };
}

/// <summary>
/// The fully linked program description recovered from the metadata file and the native binary: assemblies,
/// types, members, generic instantiations, and where each method's machine code lives.
/// </summary>
public sealed class Il2CppModel
{
    public NativeImage Image { get; }
    public MetadataFile Metadata { get; }
    public Il2CppBinary Binary { get; }
    public UnityVersion? UnityVersion { get; init; }
    public int Version => Binary.Version;
    public SigFactory Sigs { get; } = new();

    public AssemblyModel[] Assemblies = [];
    public TypeDef[] Types = [];
    public MethodDef[] Methods = [];
    public FieldDef[] Fields = [];
    public ParamDef[] Parameters = [];
    public GenericParam[] GenericParams = [];
    public MethodInst[] MethodInsts = [];

    /// <summary>Methods whose own compiled body starts at an address (several after identical-code folding).</summary>
    public Dictionary<ulong, List<MethodDef>> MethodsByAddress { get; } = [];

    /// <summary>Generic instantiations whose compiled body starts at an address.</summary>
    public Dictionary<ulong, List<MethodInst>> InstsByAddress { get; } = [];

    private readonly TypeSig?[] _sigByTypeIndex;
    private readonly Dictionary<string, TypeDef> _typesByName = new(StringComparer.Ordinal);
    private readonly Dictionary<ulong, MetadataUsage> _legacyUsages = [];
    // (Asked by every thread that recovers methods.)
    private readonly System.Collections.Concurrent.ConcurrentDictionary<ulong, MetadataUsage?> _usageCache = new();

    public Il2CppModel(NativeImage image, MetadataFile metadata, Il2CppBinary binary)
    {
        Image = image;
        Metadata = metadata;
        Binary = binary;
        _sigByTypeIndex = new TypeSig?[binary.Types.Count];
        Build();
    }

    // ---- loading with layout probing -------------------------------------------------------------------------

    /// <summary>
    /// Loads a model, choosing the exact metadata layout. When the Unity version is known it decides the layout;
    /// otherwise each layout sharing the file's version number is tried until one is fully consistent.
    /// </summary>
    public static Il2CppModel Load(NativeImage image, byte[] metadataBytes, UnityVersion? unity = null,
        Action<string>? log = null)
    {
        if (!MetadataFile.HasMagic(metadataBytes))
            throw new MetadataFormatException(
                "The metadata file does not start with the IL2CPP signature (0xFAB11BAF). It is either not a " +
                "global-metadata.dat file or it has been encrypted/obfuscated by the game's protection, which this " +
                "tool does not attempt to undo.", notStandardFormat: true);

        int major = MetadataFile.ReadMajorVersion(metadataBytes);
        if (major < MetaVersion.MinSupportedMajor || major > MetaVersion.MaxSupportedMajor)
            throw new MetadataFormatException(
                $"Metadata version {major} is not supported (supported: {MetaVersion.MinSupportedMajor}-{MetaVersion.MaxSupportedMajor}).");

        var candidates = new List<int>();
        if (unity is { } u && MetaVersion.FromUnity(major, u) is { } exact) candidates.Add(exact);
        foreach (int c in MetaVersion.Candidates(major))
            if (!candidates.Contains(c))
                candidates.Add(c);

        var failures = new List<string>();
        Il2CppBinary.Anchors? anchors = null;
        foreach (int candidate in candidates)
        {
            try
            {
                MetadataFile metadata = MetadataFile.Parse(metadataBytes, candidate);
                anchors ??= Il2CppBinary.FindAnchors(image, metadata);
                Il2CppBinary binary = Il2CppBinary.Load(image, metadata, candidate, anchors);
                log?.Invoke($"metadata layout {MetaVersion.Describe(candidate)} accepted");
                return new Il2CppModel(image, metadata, binary) { UnityVersion = unity };
            }
            catch (Exception e) when (e is MetadataFormatException or RegistrationNotFoundException)
            {
                failures.Add($"{MetaVersion.Describe(candidate)}: {e.Message}");
                log?.Invoke($"metadata layout {MetaVersion.Describe(candidate)} rejected: {e.Message}");
            }
        }
        throw new MetadataFormatException(
            "No known metadata layout fits this binary/metadata pair:\n  " + string.Join("\n  ", failures));
    }

    // ---- construction ----------------------------------------------------------------------------------------

    private void Build()
    {
        MetadataFile md = Metadata;

        Assemblies = new AssemblyModel[md.Images.Length];
        for (int i = 0; i < md.Images.Length; i++)
        {
            ImageRow im = md.Images[i];
            var asm = new AssemblyModel
            {
                Index = i,
                ImageName = im.Name,
                Name = im.Name.EndsWith(".dll", StringComparison.OrdinalIgnoreCase) ? im.Name[..^4] : im.Name,
                CustomAttributeStart = im.CustomAttributeStart,
                CustomAttributeCount = (int)im.CustomAttributeCount,
            };
            if (im.AssemblyIndex >= 0 && im.AssemblyIndex < md.Assemblies.Length)
            {
                AssemblyRow a = md.Assemblies[im.AssemblyIndex];
                if (a.Name.Length != 0) asm.Name = a.Name;
                asm.Version = new Version(Clamp(a.Major), Clamp(a.Minor), Clamp(a.Build), Clamp(a.Revision));
                asm.Culture = md.GetString(a.CultureIndex);
                asm.PublicKeyToken = a.PublicKeyToken;
                asm.Flags = a.Flags;
                asm.HashAlg = a.HashAlg;
                asm.Token = a.Token;
            }
            Binary.ModulesByName.TryGetValue(im.Name, out asm.Module);
            Assemblies[i] = asm;
        }

        // Assembly references.
        for (int i = 0; i < md.Images.Length; i++)
        {
            int ai = md.Images[i].AssemblyIndex;
            if (ai < 0 || ai >= md.Assemblies.Length) continue;
            AssemblyRow a = md.Assemblies[ai];
            for (int k = 0; k < a.ReferencedAssemblyCount; k++)
            {
                int slot = a.ReferencedAssemblyStart + k;
                if (slot < 0 || slot >= md.ReferencedAssemblies.Length) break;
                int target = md.ReferencedAssemblies[slot];
                if (target < 0 || target >= md.Assemblies.Length) continue;
                int imageIndex = md.Assemblies[target].ImageIndex;
                if (imageIndex >= 0 && imageIndex < Assemblies.Length) Assemblies[i].References.Add(Assemblies[imageIndex]);
            }
        }

        // Type shells.
        Types = new TypeDef[md.Types.Length];
        for (int a = 0; a < md.Images.Length; a++)
        {
            ImageRow im = md.Images[a];
            for (int t = im.TypeStart; t < im.TypeStart + (int)im.TypeCount; t++)
            {
                ref readonly TypeDefRow row = ref md.Types[t];
                var def = new TypeDef
                {
                    Index = t,
                    Assembly = Assemblies[a],
                    Name = md.GetString(row.NameIndex),
                    Namespace = md.GetString(row.NamespaceIndex),
                    Flags = row.Flags,
                    Token = row.Token,
                    IsValueType = row.IsValueType,
                    IsEnum = row.IsEnum,
                    HasFinalizer = row.HasFinalizer,
                    HasStaticConstructor = row.HasStaticConstructor,
                    IsBlittable = row.IsBlittable,
                    IsByRefLike = row.IsByRefLike,
                    PackingSizeIsDefault = row.PackingSizeIsDefault || Version < MetaVersion.V24_2,
                    ClassSizeIsDefault = row.ClassSizeIsDefault || Version < MetaVersion.V24_2,
                    PackingSize = DecodePackingSize(Version >= MetaVersion.V24_2 ? row.SpecifiedPackingSizeCode : row.PackingSizeCode),
                    CustomAttributeIndex = row.CustomAttributeIndex,
                };
                if (t < Binary.TypeSizes.Length) def.Sizes = Binary.TypeSizes[t];
                Types[t] = def;
                Assemblies[a].Types.Add(def);
            }
        }
        for (int t = 0; t < Types.Length; t++)
            Types[t] ??= new TypeDef { Index = t, Assembly = Assemblies[0], Name = "<orphan" + t + ">" };

        // Nesting comes from the nested-type table (declaringTypeIndex is a type index, resolved later).
        for (int t = 0; t < Types.Length; t++)
        {
            ref readonly TypeDefRow row = ref md.Types[t];
            for (int k = 0; k < row.NestedTypeCount; k++)
            {
                int slot = row.NestedTypesStart + k;
                if (slot < 0 || slot >= md.NestedTypes.Length) break;
                int nested = md.NestedTypes[slot];
                if (nested < 0 || nested >= Types.Length) continue;
                Types[nested].DeclaringType = Types[t];
                Types[t].NestedTypes.Add(Types[nested]);
            }
        }
        foreach (TypeDef def in Types) _typesByName.TryAdd(def.ReflectionName, def);

        // Generic parameters (owners are attached while reading containers below).
        GenericParams = new GenericParam[md.GenericParameters.Length];
        for (int i = 0; i < GenericParams.Length; i++)
        {
            GenericParameterRow row = md.GenericParameters[i];
            GenericParams[i] = new GenericParam
            {
                Index = i,
                Name = md.GetString(row.NameIndex),
                Position = row.Num,
                Flags = row.Flags,
            };
        }

        GenericParam[] ContainerParams(int containerIndex, TypeDef? ownerType, MethodDef? ownerMethod)
        {
            if (containerIndex < 0 || containerIndex >= md.GenericContainers.Length) return [];
            GenericContainerRow c = md.GenericContainers[containerIndex];
            if (c.TypeArgc <= 0 || c.GenericParameterStart < 0 ||
                c.GenericParameterStart + c.TypeArgc > GenericParams.Length) return [];
            var result = new GenericParam[c.TypeArgc];
            for (int k = 0; k < c.TypeArgc; k++)
            {
                GenericParam p = GenericParams[c.GenericParameterStart + k];
                p.OwnerType = ownerType;
                p.OwnerMethod = ownerMethod;
                p.IsMethodParameter = ownerMethod != null;
                result[k] = p;
            }
            return result;
        }

        for (int t = 0; t < Types.Length; t++)
            Types[t].GenericParameters = ContainerParams(md.Types[t].GenericContainerIndex, Types[t], null);

        // Members.
        Methods = new MethodDef[md.Methods.Length];
        Fields = new FieldDef[md.Fields.Length];
        Parameters = new ParamDef[md.Parameters.Length];

        for (int t = 0; t < Types.Length; t++)
        {
            TypeDef def = Types[t];
            TypeDefRow row = md.Types[t];

            def.Methods = new MethodDef[row.MethodCount];
            for (int k = 0; k < row.MethodCount; k++)
            {
                int mi = row.MethodStart + k;
                MethodDefRow mr = md.Methods[mi];
                var method = new MethodDef
                {
                    Index = mi,
                    DeclaringType = def,
                    Name = md.GetString(mr.NameIndex),
                    Flags = mr.Flags,
                    ImplFlags = mr.ImplFlags,
                    Slot = mr.Slot,
                    Token = mr.Token,
                    ReturnParameterToken = mr.ReturnParameterToken,
                    CustomAttributeIndex = mr.CustomAttributeIndex,
                };
                method.GenericParameters = ContainerParams(mr.GenericContainerIndex, null, method);
                Methods[mi] = method;
                def.Methods[k] = method;
            }

            def.Fields = new FieldDef[row.FieldCount];
            for (int k = 0; k < row.FieldCount; k++)
            {
                int fi = row.FieldStart + k;
                FieldDefRow fr = md.Fields[fi];
                var field = new FieldDef
                {
                    Index = fi,
                    DeclaringType = def,
                    Name = md.GetString(fr.NameIndex),
                    Token = fr.Token,
                    Offset = Binary.GetFieldOffset(t, k),
                    CustomAttributeIndex = fr.CustomAttributeIndex,
                };
                Fields[fi] = field;
                def.Fields[k] = field;
            }
        }
        for (int i = 0; i < Methods.Length; i++)
            Methods[i] ??= new MethodDef { Index = i, DeclaringType = Types[0], Name = "<orphan" + i + ">" };
        for (int i = 0; i < Fields.Length; i++)
            Fields[i] ??= new FieldDef { Index = i, DeclaringType = Types[0], Name = "<orphan" + i + ">" };

        // Signatures: now that all definitions and generic parameters exist, types can be resolved.
        for (int t = 0; t < Types.Length; t++)
        {
            TypeDef def = Types[t];
            TypeDefRow row = md.Types[t];
            def.Sig = TypeAt(row.ByvalTypeIndex) ?? Sigs.TypeDef(def);
            def.BaseType = TypeAt(row.ParentIndex);

            def.Interfaces = new TypeSig[row.InterfacesCount];
            for (int k = 0; k < row.InterfacesCount; k++)
                def.Interfaces[k] = TypeAt(md.Interfaces[row.InterfacesStart + k]) ?? Sigs.Opaque(SigKind.Unknown, "?");

            def.VTable = row.VtableCount == 0 || row.VtableStart < 0
                ? []
                : md.VTableMethods.AsSpan(row.VtableStart, row.VtableCount).ToArray();

            def.InterfaceOffsets = new (TypeSig, int)[row.InterfaceOffsetsCount];
            for (int k = 0; k < row.InterfaceOffsetsCount; k++)
            {
                InterfaceOffsetRow io = md.InterfaceOffsets[row.InterfaceOffsetsStart + k];
                def.InterfaceOffsets[k] = (TypeAt(io.InterfaceTypeIndex) ?? Sigs.Opaque(SigKind.Unknown, "?"), io.Offset);
            }

            foreach (FieldDef field in def.Fields)
            {
                int typeIndex = md.Fields[field.Index].TypeIndex;
                field.Type = TypeAt(typeIndex) ?? Sigs.Opaque(SigKind.Unknown, "?");
                if (typeIndex >= 0 && typeIndex < Binary.Types.Count) field.Attrs = Binary.Types[typeIndex].Attrs;
            }

            foreach (MethodDef method in def.Methods)
            {
                MethodDefRow mr = md.Methods[method.Index];
                method.ReturnType = TypeAt(mr.ReturnType) ?? Sigs.Opaque(SigKind.Unknown, "?");
                method.Parameters = new ParamDef[mr.ParameterCount];
                for (int k = 0; k < mr.ParameterCount; k++)
                {
                    int pi = mr.ParameterStart + k;
                    ParameterDefRow pr = md.Parameters[pi];
                    var p = new ParamDef
                    {
                        Index = pi,
                        Position = k,
                        Name = md.GetString(pr.NameIndex),
                        Token = pr.Token,
                        Type = TypeAt(pr.TypeIndex) ?? Sigs.Opaque(SigKind.Unknown, "?"),
                        CustomAttributeIndex = pr.CustomAttributeIndex,
                    };
                    if (pr.TypeIndex >= 0 && pr.TypeIndex < Binary.Types.Count) p.Attrs = Binary.Types[pr.TypeIndex].Attrs;
                    Parameters[pi] = p;
                    method.Parameters[k] = p;
                }
                ResolveMethodAddress(method, mr);
            }

            def.Properties = new PropertyDef[row.PropertyCount];
            for (int k = 0; k < row.PropertyCount; k++)
            {
                PropertyDefRow pr = md.Properties[row.PropertyStart + k];
                def.Properties[k] = new PropertyDef
                {
                    DeclaringType = def,
                    Name = md.GetString(pr.NameIndex),
                    Getter = pr.Get >= 0 && pr.Get < def.Methods.Length ? def.Methods[pr.Get] : null,
                    Setter = pr.Set >= 0 && pr.Set < def.Methods.Length ? def.Methods[pr.Set] : null,
                    Attrs = pr.Attrs,
                    Token = pr.Token,
                    CustomAttributeIndex = pr.CustomAttributeIndex,
                };
            }

            def.Events = new EventDef[row.EventCount];
            for (int k = 0; k < row.EventCount; k++)
            {
                EventDefRow er = md.Events[row.EventStart + k];
                def.Events[k] = new EventDef
                {
                    DeclaringType = def,
                    Name = md.GetString(er.NameIndex),
                    Type = TypeAt(er.TypeIndex) ?? Sigs.Opaque(SigKind.Unknown, "?"),
                    Add = er.Add >= 0 && er.Add < def.Methods.Length ? def.Methods[er.Add] : null,
                    Remove = er.Remove >= 0 && er.Remove < def.Methods.Length ? def.Methods[er.Remove] : null,
                    Raise = er.Raise >= 0 && er.Raise < def.Methods.Length ? def.Methods[er.Raise] : null,
                    Token = er.Token,
                    CustomAttributeIndex = er.CustomAttributeIndex,
                };
            }

            if (def.IsEnum)
            {
                // v35 dropped elementTypeIndex and reuses parentIndex for the underlying type of enums; the
                // runtime then sets the parent to System.Enum (GlobalMetadata.cpp, FromTypeDefinition).
                if (Version >= MetaVersion.V35)
                {
                    def.EnumUnderlyingType = def.BaseType;
                    def.BaseType = null; // patched to System.Enum once all types are known
                }
                else
                {
                    def.EnumUnderlyingType = TypeAt(row.ElementTypeIndex);
                }
                if (def.EnumUnderlyingType is not PrimitiveSig)
                {
                    foreach (FieldDef field in def.Fields)
                        if (!field.IsStatic)
                        {
                            def.EnumUnderlyingType = field.Type;
                            break;
                        }
                }
            }
        }

        if (Version >= MetaVersion.V35 && FindType("System.Enum") is { } enumBase)
        {
            foreach (TypeDef def in Types)
                if (def.IsEnum && def.BaseType == null)
                    def.BaseType = enumBase.Sig;
        }

        // Generic parameter constraints.
        for (int i = 0; i < GenericParams.Length; i++)
        {
            GenericParameterRow row = md.GenericParameters[i];
            if (row.ConstraintsCount <= 0) continue;
            var constraints = new List<TypeSig>();
            for (int k = 0; k < row.ConstraintsCount; k++)
            {
                int slot = row.ConstraintsStart + k;
                if (slot < 0 || slot >= md.GenericParameterConstraints.Length) break;
                if (TypeAt(md.GenericParameterConstraints[slot]) is { } c) constraints.Add(c);
            }
            GenericParams[i].Constraints = constraints.ToArray();
        }

        // Default values.
        foreach (DefaultValueRow dv in md.FieldDefaultValues)
        {
            if (dv.OwnerIndex < 0 || dv.OwnerIndex >= Fields.Length) continue;
            FieldDef f = Fields[dv.OwnerIndex];
            f.HasDefault = true;
            f.DefaultTypeIndex = dv.TypeIndex;
            f.DefaultDataIndex = dv.DataIndex;
        }
        foreach (DefaultValueRow dv in md.ParameterDefaultValues)
        {
            if (dv.OwnerIndex < 0 || dv.OwnerIndex >= Parameters.Length || Parameters[dv.OwnerIndex] == null) continue;
            ParamDef p = Parameters[dv.OwnerIndex];
            p.HasDefault = true;
            p.DefaultTypeIndex = dv.TypeIndex;
            p.DefaultDataIndex = dv.DataIndex;
        }

        // Delegates.
        TypeDef? multicast = FindType("System.MulticastDelegate");
        TypeDef? delegateType = FindType("System.Delegate");
        foreach (TypeDef def in Types)
        {
            TypeDef? b = def.BaseType?.Definition;
            def.IsDelegate = b != null && (b == multicast || (b == delegateType && def != multicast));
        }

        // Entry points.
        for (int i = 0; i < md.Images.Length; i++)
        {
            int ep = md.Images[i].EntryPointIndex;
            if (ep >= 0 && ep < Methods.Length) Assemblies[i].EntryPoint = Methods[ep];
        }

        BuildMethodInsts();
        BuildLegacyUsages();
    }

    private static int Clamp(int v) => Math.Clamp(v, 0, ushort.MaxValue);

    private static int DecodePackingSize(int code) => code switch
    {
        0 => 0, 1 => 1, 2 => 2, 3 => 4, 4 => 8, 5 => 16, 6 => 32, 7 => 64, 8 => 128, _ => 0,
    };

    private void ResolveMethodAddress(MethodDef method, MethodDefRow row)
    {
        ulong address = 0;
        if (Version >= MetaVersion.V24_2)
        {
            RawCodeGenModule? module = method.DeclaringType.Assembly.Module;
            int rid = (int)(row.Token & 0xFFFFFF);
            if (module != null && rid >= 1 && rid <= module.MethodPointers.Length)
            {
                address = module.MethodPointers[rid - 1];
                if (rid <= module.InvokerIndices.Length) method.InvokerIndex = module.InvokerIndices[rid - 1];
                if (module.AdjustorThunks.TryGetValue(row.Token, out ulong thunk)) method.AdjustorThunk = thunk;
            }
        }
        else if (row.MethodIndex >= 0 && row.MethodIndex < Binary.GlobalMethodPointers.Length)
        {
            address = Binary.GlobalMethodPointers[row.MethodIndex];
            method.InvokerIndex = row.InvokerIndex;
        }

        // ARM32 function pointers carry the Thumb bit; code starts at the even address.
        if (Image.Arch == CpuArch.Arm32) address &= ~1UL;
        if (address == 0 || !Image.IsCodeAddress(address)) return;
        method.Address = address;
        if (!MethodsByAddress.TryGetValue(address, out List<MethodDef>? list)) MethodsByAddress[address] = list = [];
        list.Add(method);
    }

    private void BuildMethodInsts()
    {
        TypeSig[] Args(int instIndex)
        {
            if (instIndex < 0 || instIndex >= Binary.GenericInsts.Count) return [];
            int[] indexes = Binary.GenericInsts[instIndex].TypeArgs;
            var args = new TypeSig[indexes.Length];
            for (int i = 0; i < indexes.Length; i++)
                args[i] = TypeAt(indexes[i]) ?? Sigs.Opaque(SigKind.Unknown, "?");
            return args;
        }

        MethodInsts = new MethodInst[Binary.MethodSpecs.Length];
        for (int i = 0; i < MethodInsts.Length; i++)
        {
            RawMethodSpec spec = Binary.MethodSpecs[i];
            MethodDef method = spec.MethodDefinitionIndex >= 0 && spec.MethodDefinitionIndex < Methods.Length
                ? Methods[spec.MethodDefinitionIndex]
                : Methods[0];
            MethodInsts[i] = new MethodInst
            {
                SpecIndex = i,
                Method = method,
                ClassArguments = Args(spec.ClassInstIndex),
                MethodArguments = Args(spec.MethodInstIndex),
            };
        }

        foreach (RawGenericMethodFunction g in Binary.GenericMethodTable)
        {
            if (g.MethodSpecIndex < 0 || g.MethodSpecIndex >= MethodInsts.Length) continue;
            MethodInst inst = MethodInsts[g.MethodSpecIndex];
            inst.InvokerIndex = g.InvokerIndex;
            if (g.MethodPointerIndex >= 0 && g.MethodPointerIndex < Binary.GenericMethodPointers.Length)
            {
                ulong address = Binary.GenericMethodPointers[g.MethodPointerIndex];
                if (Image.Arch == CpuArch.Arm32) address &= ~1UL;
                if (address != 0 && Image.IsCodeAddress(address))
                {
                    inst.Address = address;
                    if (!InstsByAddress.TryGetValue(address, out List<MethodInst>? list)) InstsByAddress[address] = list = [];
                    list.Add(inst);
                }
            }
            if (g.AdjustorThunkIndex >= 0 && g.AdjustorThunkIndex < Binary.GenericAdjustorThunks.Length)
                inst.AdjustorThunk = Binary.GenericAdjustorThunks[g.AdjustorThunkIndex];
        }
    }

    // ---- lookups ---------------------------------------------------------------------------------------------

    /// <summary>Resolved signature for an index into the binary's Il2CppType table; null for -1 / out of range.</summary>
    public TypeSig? TypeAt(int typeIndex)
    {
        if (typeIndex < 0 || typeIndex >= Binary.Types.Count) return null;
        if (typeIndex < _sigByTypeIndex.Length && _sigByTypeIndex[typeIndex] is { } cached) return cached;
        TypeSig sig = ResolveRaw(Binary.Types[typeIndex]);
        if (typeIndex < _sigByTypeIndex.Length) _sigByTypeIndex[typeIndex] = sig;
        return sig;
    }

    private TypeSig ResolveRaw(RawType t)
    {
        TypeSig core;
        switch (t.Type)
        {
            case Il2CppTypeEnum.Class:
            case Il2CppTypeEnum.ValueType:
                core = t.DefinitionIndex >= 0 && t.DefinitionIndex < Types.Length
                    ? Sigs.TypeDef(Types[t.DefinitionIndex])
                    : Sigs.Opaque(SigKind.Unknown, "?type" + t.DefinitionIndex);
                break;
            case Il2CppTypeEnum.Var:
            case Il2CppTypeEnum.MVar:
                core = t.DefinitionIndex >= 0 && t.DefinitionIndex < GenericParams.Length
                    ? Sigs.GenericParam(GenericParams[t.DefinitionIndex])
                    : Sigs.Opaque(SigKind.Unknown, "?gp" + t.DefinitionIndex);
                break;
            case Il2CppTypeEnum.Ptr:
                core = Sigs.Pointer(TypeAt(t.ElementType) ?? Sigs.Primitive(Il2CppTypeEnum.Void));
                break;
            case Il2CppTypeEnum.SzArray:
                core = Sigs.SzArray(TypeAt(t.ElementType) ?? Sigs.Primitive(Il2CppTypeEnum.Object));
                break;
            case Il2CppTypeEnum.Array:
                core = Sigs.Array(TypeAt(t.ElementType) ?? Sigs.Primitive(Il2CppTypeEnum.Object), Math.Max(1, t.ArrayRank));
                break;
            case Il2CppTypeEnum.GenericInst:
            {
                if (t.GenericTypeDefinition < 0 || t.GenericTypeDefinition >= Types.Length ||
                    t.GenericInst < 0 || t.GenericInst >= Binary.GenericInsts.Count)
                {
                    core = Sigs.Opaque(SigKind.Unknown, "?generic");
                    break;
                }
                int[] argIndexes = Binary.GenericInsts[t.GenericInst].TypeArgs;
                var args = new TypeSig[argIndexes.Length];
                for (int i = 0; i < args.Length; i++)
                    args[i] = TypeAt(argIndexes[i]) ?? Sigs.Opaque(SigKind.Unknown, "?");
                core = Sigs.GenericInst(Types[t.GenericTypeDefinition], args);
                break;
            }
            case Il2CppTypeEnum.FnPtr:
                core = Sigs.Opaque(SigKind.FunctionPointer, "delegate*<...>");
                break;
            case Il2CppTypeEnum.Void:
            case Il2CppTypeEnum.Boolean:
            case Il2CppTypeEnum.Char:
            case Il2CppTypeEnum.I1:
            case Il2CppTypeEnum.U1:
            case Il2CppTypeEnum.I2:
            case Il2CppTypeEnum.U2:
            case Il2CppTypeEnum.I4:
            case Il2CppTypeEnum.U4:
            case Il2CppTypeEnum.I8:
            case Il2CppTypeEnum.U8:
            case Il2CppTypeEnum.R4:
            case Il2CppTypeEnum.R8:
            case Il2CppTypeEnum.String:
            case Il2CppTypeEnum.I:
            case Il2CppTypeEnum.U:
            case Il2CppTypeEnum.Object:
            case Il2CppTypeEnum.TypedByRef:
                core = Sigs.Primitive(t.Type,
                    t.DefinitionIndex >= 0 && t.DefinitionIndex < Types.Length ? Types[t.DefinitionIndex] : null);
                break;
            default:
                core = Sigs.Opaque(SigKind.Unknown, "?" + t.Type);
                break;
        }
        return t.ByRef ? Sigs.ByRef(core) : core;
    }

    /// <summary>Finds a type by reflection-style name, e.g. "System.Collections.Generic.List`1".</summary>
    public TypeDef? FindType(string reflectionName) => _typesByName.GetValueOrDefault(reflectionName);

    public static (UsageKind Kind, int Index) DecodeUsageToken(uint encoded, int version)
    {
        var kind = (UsageKind)((encoded & 0xE0000000) >> 29);
        int index = version >= MetaVersion.V27_0 ? (int)((encoded & 0x1FFFFFFE) >> 1) : (int)(encoded & 0x1FFFFFFF);
        return (kind, index);
    }

    public (MethodDef? Method, MethodInst? Inst) DecodeVTableEntry(uint encoded)
    {
        var (kind, index) = DecodeUsageToken(encoded, Version);
        return kind switch
        {
            UsageKind.MethodDef when index >= 0 && index < Methods.Length => (Methods[index], null),
            UsageKind.MethodRef when index >= 0 && index < MethodInsts.Length => (MethodInsts[index].Method, MethodInsts[index]),
            _ => (null, null),
        };
    }

    private MetadataUsage? MakeUsage(UsageKind kind, int index)
    {
        switch (kind)
        {
            case UsageKind.TypeInfo:
            case UsageKind.Il2CppType:
                return TypeAt(index) is { } type ? new MetadataUsage(kind, index) { Type = type } : null;
            case UsageKind.MethodDef:
                return index >= 0 && index < Methods.Length ? new MetadataUsage(kind, index) { Method = Methods[index] } : null;
            case UsageKind.MethodRef:
                return index >= 0 && index < MethodInsts.Length
                    ? new MetadataUsage(kind, index) { MethodInst = MethodInsts[index], Method = MethodInsts[index].Method }
                    : null;
            case UsageKind.FieldInfo:
            case UsageKind.FieldRva:
            {
                if (index < 0 || index >= Metadata.FieldRefs.Length) return null;
                FieldRefRow fr = Metadata.FieldRefs[index];
                TypeSig? owner = TypeAt(fr.TypeIndex);
                TypeDef? def = owner?.Definition;
                if (def == null || fr.FieldIndex < 0 || fr.FieldIndex >= def.Fields.Length) return null;
                return new MetadataUsage(kind, index) { Type = owner, Field = def.Fields[fr.FieldIndex] };
            }
            case UsageKind.StringLiteral:
                return index >= 0 && index < Metadata.StringLiteralCount
                    ? new MetadataUsage(kind, index) { String = Metadata.GetStringLiteral(index) }
                    : null;
            default:
                return null;
        }
    }

    private void BuildLegacyUsages()
    {
        if (Version >= MetaVersion.V27_0) return;
        foreach (MetadataUsagePairRow pair in Metadata.MetadataUsagePairs)
        {
            if (pair.DestinationIndex >= (uint)Binary.MetadataUsageSlots.Length) continue;
            var (kind, index) = DecodeUsageToken(pair.EncodedSourceIndex, Version);
            if (MakeUsage(kind, index) is { } usage)
                _legacyUsages[Binary.MetadataUsageSlots[pair.DestinationIndex]] = usage;
        }
    }

    private Dictionary<(string Image, uint Token), RgctxItem[]>? _rgctx;
    private readonly object _rgctxLock = new();

    /// <summary>
    /// The runtime generic context declared for a generic type or method definition: the classes, types and
    /// methods its shared code looks up at run time, written in terms of the definition's own type parameters.
    /// Empty when the definition has none.
    /// </summary>
    public IReadOnlyList<RgctxItem> RgctxOf(string imageName, uint token)
    {
        lock (_rgctxLock)
        {
            if (_rgctx == null)
            {
                var all = new Dictionary<(string, uint), RgctxItem[]>();
                foreach (RawCodeGenModule module in Binary.Modules)
                    foreach (RawRgctxRange range in module.RgctxRanges)
                    {
                        if (range.Start < 0 || range.Length <= 0 || range.Start + range.Length > module.Rgctxs.Length) continue;
                        var items = new RgctxItem[range.Length];
                        for (int i = 0; i < items.Length; i++)
                        {
                            RawRgctxEntry e = module.Rgctxs[range.Start + i];
                            items[i] = e.Kind switch
                            {
                                RgctxKind.Type or RgctxKind.Class or RgctxKind.Array => new RgctxItem(e.Kind, TypeAt(e.Index), null),
                                RgctxKind.Method => new RgctxItem(e.Kind, null, e.Index >= 0 && e.Index < MethodInsts.Length ? MethodInsts[e.Index] : null),
                                _ => new RgctxItem(e.Kind, null, null),
                            };
                        }
                        all[(module.Name, range.Token)] = items;
                    }
                _rgctx = all;
            }
            return _rgctx.TryGetValue((imageName, token), out RgctxItem[]? found) ? found : [];
        }
    }

    /// <summary>
    /// Resolves the global slot at <paramref name="va"/> to the metadata item the runtime will store there.
    /// From v27 the slot's initial value is the encoded token itself; before that a side table maps slots.
    /// </summary>
    public MetadataUsage? ResolveUsageSlot(ulong va)
    {
        if (_usageCache.TryGetValue(va, out MetadataUsage? cached)) return cached;
        MetadataUsage? result = null;
        if (Version < MetaVersion.V27_0)
        {
            _legacyUsages.TryGetValue(va, out result);
        }
        else if (Image.IsMapped(va, Image.PointerSize))
        {
            ulong raw = Image.Ptr(va);
            // Uninitialized slots hold (kind << 29 | index << 1 | 1); real pointers are aligned, so bit 0 is clear.
            if (raw <= uint.MaxValue && (raw & 1) != 0)
            {
                var (kind, index) = DecodeUsageToken((uint)raw, Version);
                result = MakeUsage(kind, index);
            }
        }
        return _usageCache.GetOrAdd(va, result);
    }
}
