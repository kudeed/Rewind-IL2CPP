using System.Text;
using Rewind.Binary;
using Rewind.Metadata;

namespace Rewind.Runtime;

public sealed class RegistrationNotFoundException(string message) : Exception(message);

/// <summary>
/// The IL2CPP registration data inside the native binary: where each method's code is, the Il2CppType table,
/// generic instantiations, field offsets and per-assembly code generation modules.
/// </summary>
public sealed class Il2CppBinary
{
    public NativeImage Image { get; }
    public int Version { get; }
    public ulong CodeRegistrationVa { get; private set; }
    public ulong MetadataRegistrationVa { get; private set; }

    public ulong[] GenericMethodPointers = [];
    public ulong[] GenericAdjustorThunks = [];
    public ulong[] InvokerPointers = [];
    public ulong[] ReversePInvokeWrappers = [];
    public ulong[] UnresolvedVirtualCallPointers = [];
    public ulong[] UnresolvedInstanceCallPointers = [];
    public ulong[] UnresolvedStaticCallPointers = [];
    public ulong[] CustomAttributeGenerators = [];

    /// <summary>Up to v24.15: one global method pointer table indexed by MethodDefRow.MethodIndex.</summary>
    public ulong[] GlobalMethodPointers = [];

    public RawCodeGenModule[] Modules = [];
    public Dictionary<string, RawCodeGenModule> ModulesByName { get; } = new(StringComparer.Ordinal);

    /// <summary>All Il2CppType records. The first <see cref="TableTypeCount"/> are the registered type table.</summary>
    public List<RawType> Types { get; } = [];
    public int TableTypeCount { get; private set; }
    public List<RawGenericInst> GenericInsts { get; } = [];
    public int TableGenericInstCount { get; private set; }

    public RawMethodSpec[] MethodSpecs = [];
    public RawGenericMethodFunction[] GenericMethodTable = [];
    public RawTypeSizes[] TypeSizes = [];
    public ulong[] FieldOffsetPointers = [];
    public ulong[] GenericClassPointers = [];

    /// <summary>Pre-v27: addresses of the global slots that metadata usage pairs refer to by index.</summary>
    public ulong[] MetadataUsageSlots = [];

    private readonly Dictionary<ulong, int> _typeIndexByVa = [];
    private readonly Dictionary<ulong, int> _genericInstIndexByVa = [];
    private readonly int _ps;

    private Il2CppBinary(NativeImage image, int version)
    {
        Image = image;
        Version = version;
        _ps = image.PointerSize;
    }

    // ---- locating the registration structs ---------------------------------------------------------------------

    /// <summary>Version-independent anchors found by searching the image's data.</summary>
    public sealed record Anchors(ulong CodeGenModulesArray, ulong CodeGenModulesSlot, ulong MetadataRegistration,
        ulong GlobalMethodPointersSlot);

    /// <summary>
    /// Finds the code generation module array (via the pointer chain "mscorlib.dll" string -> module -> module
    /// array -> code registration) and the metadata registration (via its two type-definition-count fields).
    /// </summary>
    public static Anchors FindAnchors(NativeImage image, MetadataFile metadata)
    {
        ulong modulesArray = 0, modulesSlot = 0;
        int imageCount = metadata.Images.Length;
        var imageNames = new HashSet<string>(metadata.Images.Select(i => i.Name), StringComparer.Ordinal);
        ulong ps = (ulong)image.PointerSize;

        bool IsModulePointer(ulong p)
        {
            if (p == 0 || !image.TryPtr(p, out ulong namePtr)) return false;
            string? name = image.TryCString(namePtr, 300);
            return name != null && imageNames.Contains(name);
        }

        byte[] needle = Encoding.ASCII.GetBytes("mscorlib.dll\0");
        foreach (ulong str in image.FindBytes(needle))
        {
            foreach (ulong module in image.FindPointersTo(str))
            {
                foreach (ulong slot in image.FindPointersTo(module))
                {
                    // Extend to the full run of valid module pointers around this slot.
                    ulong first = slot;
                    while (image.TryPtr(first - ps, out ulong prev) && IsModulePointer(prev)) first -= ps;
                    ulong last = slot;
                    while (image.TryPtr(last + ps, out ulong next) && IsModulePointer(next)) last += ps;
                    int run = (int)((last - first) / ps) + 1;
                    if (run < imageCount) continue;

                    // The registration holds a pointer to the array start preceded by its element count.
                    for (ulong start = first; start + (ulong)imageCount * ps <= last + ps; start += ps)
                    {
                        foreach (ulong reference in image.FindPointersTo(start))
                        {
                            if (!image.IsMapped(reference - ps, image.PointerSize)) continue;
                            if (image.NInt(reference - ps) != imageCount) continue;
                            modulesArray = start;
                            modulesSlot = reference;
                            break;
                        }
                        if (modulesArray != 0) break;
                    }
                    if (modulesArray != 0) break;
                }
                if (modulesArray != 0) break;
            }
            if (modulesArray != 0) break;
        }

        ulong metadataRegistration = FindMetadataRegistration(image, metadata);
        ulong globalMethodPointersSlot = modulesArray == 0 ? FindGlobalMethodPointers(image, metadata) : 0;
        return new Anchors(modulesArray, modulesSlot, metadataRegistration, globalMethodPointersSlot);
    }

    private static ulong FindMetadataRegistration(NativeImage image, MetadataFile metadata)
    {
        // fieldOffsetsCount and typeDefinitionsSizesCount both equal the number of type definitions and sit two
        // words apart, each followed by a pointer; they are words 10 and 12 of the struct.
        ulong ps = (ulong)image.PointerSize;
        ulong typeCount = (ulong)metadata.Types.Length;
        ulong best = 0;
        foreach (ulong hit in image.FindPointersTo(typeCount))
        {
            if (!image.IsMapped(hit - 10 * ps, 16 * image.PointerSize)) continue;
            if (image.Ptr(hit + 2 * ps) != typeCount) continue;
            ulong fieldOffsets = image.Ptr(hit + ps), sizes = image.Ptr(hit + 3 * ps);
            if (!image.IsMapped(fieldOffsets, image.PointerSize) || !image.IsMapped(sizes, image.PointerSize)) continue;

            ulong start = hit - 10 * ps;
            bool ok = true;
            for (int word = 0; word < 10 && ok; word += 2)
            {
                long count = image.NInt(start + (ulong)word * ps);
                ulong ptr = image.Ptr(start + (ulong)(word + 1) * ps);
                if (count < 0 || count > 0x4000000) ok = false;
                else if (count > 0 && !image.IsMapped(ptr, image.PointerSize)) ok = false;
            }
            if (!ok) continue;
            long types = image.NInt(start + 6 * ps);
            if (types <= 0) continue;
            best = start;
            break;
        }
        return best;
    }

    /// <summary>Pre-24.2 only: the code registration starts with the global method pointer table.</summary>
    private static ulong FindGlobalMethodPointers(NativeImage image, MetadataFile metadata)
    {
        int max = -1;
        foreach (ref readonly MethodDefRow m in metadata.Methods.AsSpan())
            if (m.MethodIndex > max)
                max = m.MethodIndex;
        if (max < 0) return 0;
        ulong ps = (ulong)image.PointerSize;
        foreach (ulong hit in image.FindPointersTo((ulong)(max + 1)))
        {
            if (!image.TryPtr(hit + ps, out ulong table) || !image.IsMapped(table, 4 * image.PointerSize)) continue;
            int code = 0;
            for (int i = 0; i < 4; i++)
                if (image.IsCodeAddress(image.Ptr(table + (ulong)i * ps)))
                    code++;
            if (code >= 3) return hit;
        }
        return 0;
    }

    // ---- loading -----------------------------------------------------------------------------------------------

    /// <summary>
    /// Reads the registration data assuming one specific layout version. Throws
    /// <see cref="RegistrationNotFoundException"/> when the data does not fit that layout.
    /// </summary>
    public static Il2CppBinary Load(NativeImage image, MetadataFile metadata, int version, Anchors anchors)
    {
        var b = new Il2CppBinary(image, version);
        ulong ps = (ulong)image.PointerSize;
        string L = MetaVersion.Describe(version);

        if (anchors.MetadataRegistration == 0)
            throw new RegistrationNotFoundException("Could not locate Il2CppMetadataRegistration in the binary");

        WordLayout cr = WordLayout.CodeRegistration(version);
        ulong crVa;
        if (version >= MetaVersion.V24_2)
        {
            if (anchors.CodeGenModulesSlot == 0)
                throw new RegistrationNotFoundException("Could not locate the code generation module table in the binary");
            crVa = anchors.CodeGenModulesSlot - (ulong)cr.IndexOf("codeGenModules") * ps;
        }
        else
        {
            if (anchors.GlobalMethodPointersSlot == 0)
                throw new RegistrationNotFoundException("Could not locate the global method pointer table in the binary");
            crVa = anchors.GlobalMethodPointersSlot;
        }
        if (!image.IsMapped(crVa, cr.WordCount * image.PointerSize))
            throw new RegistrationNotFoundException($"Code registration is out of range for layout {L}");

        b.CodeRegistrationVa = crVa;
        b.MetadataRegistrationVa = anchors.MetadataRegistration;

        ulong Word(string field) => image.Ptr(crVa + (ulong)cr.IndexOf(field) * ps);

        // Shifted layouts put pointers where counts belong, so strict bounds reject a wrong guess.
        foreach (string field in cr.Fields)
        {
            ulong value = Word(field);
            if (field.EndsWith("Count", StringComparison.Ordinal))
            {
                if (value > 0x1000000)
                    throw new RegistrationNotFoundException($"Code registration field {field} is implausible for layout {L}");
            }
            else if (value != 0 && !image.IsMapped(value, image.PointerSize))
            {
                throw new RegistrationNotFoundException($"Code registration field {field} is not a valid pointer for layout {L}");
            }
        }

        b.GenericMethodPointers = b.ReadPointerArray(Word("genericMethodPointers"), (int)Word("genericMethodPointersCount"));
        b.InvokerPointers = b.ReadPointerArray(Word("invokerPointers"), (int)Word("invokerPointersCount"));
        b.ReversePInvokeWrappers = b.ReadPointerArray(Word("reversePInvokeWrappers"), (int)Word("reversePInvokeWrapperCount"));
        if (cr.Has("genericAdjustorThunks"))
            b.GenericAdjustorThunks = b.ReadPointerArray(Word("genericAdjustorThunks"), (int)Word("genericMethodPointersCount"));
        int unresolved = (int)Word("unresolvedVirtualCallCount");
        b.UnresolvedVirtualCallPointers = b.ReadPointerArray(Word("unresolvedVirtualCallPointers"), unresolved);
        if (cr.Has("unresolvedInstanceCallPointers"))
        {
            b.UnresolvedInstanceCallPointers = b.ReadPointerArray(Word("unresolvedInstanceCallPointers"), unresolved);
            b.UnresolvedStaticCallPointers = b.ReadPointerArray(Word("unresolvedStaticCallPointers"), unresolved);
        }
        if (cr.Has("customAttributeGenerators"))
            b.CustomAttributeGenerators = b.ReadPointerArray(Word("customAttributeGenerators"), (int)Word("customAttributeCount"));
        if (cr.Has("methodPointers"))
            b.GlobalMethodPointers = b.ReadPointerArray(Word("methodPointers"), (int)Word("methodPointersCount"));

        RequireCode(image, b.InvokerPointers, "invoker", L);
        RequireCode(image, b.GenericMethodPointers, "generic method", L);

        if (cr.Has("codeGenModules"))
        {
            int count = (int)Word("codeGenModulesCount");
            if (count != metadata.Images.Length || Word("codeGenModules") != anchors.CodeGenModulesArray)
                throw new RegistrationNotFoundException($"Code generation module table does not line up for layout {L}");
            b.ReadModules(anchors.CodeGenModulesArray, count, metadata);
        }

        b.ReadMetadataRegistration(metadata);
        return b;
    }

    private static void RequireCode(NativeImage image, ulong[] pointers, string what, string layout)
    {
        int checkedCount = 0, code = 0;
        foreach (ulong p in pointers)
        {
            if (p == 0) continue;
            checkedCount++;
            if (image.IsCodeAddress(p)) code++;
            if (checkedCount == 16) break;
        }
        if (checkedCount > 0 && code < checkedCount)
            throw new RegistrationNotFoundException($"The {what} pointer table does not point at code for layout {layout}");
    }

    private ulong[] ReadPointerArray(ulong va, int count)
    {
        if (va == 0 || count <= 0) return [];
        if (!Image.IsMapped(va, checked(count * _ps)))
            throw new RegistrationNotFoundException($"Pointer table at 0x{va:X} ({count} entries) is out of range");
        var result = new ulong[count];
        if (_ps == 8)
            for (int i = 0; i < count; i++) result[i] = Image.U64(va + (ulong)i * 8);
        else
            for (int i = 0; i < count; i++) result[i] = Image.U32(va + (ulong)i * 4);
        return result;
    }

    private int[] ReadInt32Array(ulong va, int count)
    {
        if (va == 0 || count <= 0) return [];
        if (!Image.IsMapped(va, checked(count * 4)))
            throw new RegistrationNotFoundException($"Int table at 0x{va:X} ({count} entries) is out of range");
        var result = new int[count];
        for (int i = 0; i < count; i++) result[i] = Image.I32(va + (ulong)i * 4);
        return result;
    }

    private void ReadModules(ulong arrayVa, int count, MetadataFile metadata)
    {
        WordLayout ml = WordLayout.CodeGenModule(Version);
        ulong ps = (ulong)_ps;
        string L = MetaVersion.Describe(Version);
        Modules = new RawCodeGenModule[count];
        ulong[] modulePointers = ReadPointerArray(arrayVa, count);

        // Number of MethodDef rows per image, used to confirm the module layout.
        var methodsPerImage = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (ImageRow image in metadata.Images)
        {
            int methods = 0;
            for (int t = image.TypeStart; t < image.TypeStart + (int)image.TypeCount; t++)
                methods += metadata.Types[t].MethodCount;
            methodsPerImage[image.Name] = methods;
        }

        for (int i = 0; i < count; i++)
        {
            ulong va = modulePointers[i];
            if (!Image.IsMapped(va, ml.WordCount * _ps))
                throw new RegistrationNotFoundException($"Module {i} is out of range for layout {L}");
            ulong W(string field) => Image.Ptr(va + (ulong)ml.IndexOf(field) * ps);

            var module = new RawCodeGenModule { Va = va, Name = Image.TryCString(W("moduleName"), 300) ?? "" };
            long methodCount = (long)W("methodPointerCount");
            long rangeCount = (long)W("rgctxRangesCount"), rgctxCount = (long)W("rgctxsCount");
            if (methodCount < 0 || methodCount > 0x1000000 || rangeCount < 0 || rangeCount > 0x1000000 ||
                rgctxCount < 0 || rgctxCount > 0x1000000)
                throw new RegistrationNotFoundException($"Module '{module.Name}' has implausible counts for layout {L}");
            if (methodsPerImage.TryGetValue(module.Name, out int expected) && expected != methodCount)
                throw new RegistrationNotFoundException(
                    $"Module '{module.Name}' lists {methodCount} method pointers but the metadata has {expected} methods (layout {L})");

            module.MethodPointers = ReadPointerArray(W("methodPointers"), (int)methodCount);
            module.InvokerIndices = ReadInt32Array(W("invokerIndices"), (int)methodCount);

            if (ml.Has("adjustorThunks"))
            {
                long thunkCount = (long)W("adjustorThunkCount");
                ulong thunks = W("adjustorThunks");
                if (thunkCount < 0 || thunkCount > methodCount)
                    throw new RegistrationNotFoundException($"Module '{module.Name}' adjustor thunk count is implausible for layout {L}");
                for (long k = 0; k < thunkCount && thunks != 0; k++)
                {
                    ulong e = thunks + (ulong)k * 2 * ps;
                    module.AdjustorThunks[Image.U32(e)] = Image.Ptr(e + ps);
                }
            }

            ulong ranges = W("rgctxRanges");
            module.RgctxRanges = new RawRgctxRange[rangeCount];
            for (long k = 0; k < rangeCount && ranges != 0; k++)
            {
                ulong e = ranges + (ulong)k * 12;
                module.RgctxRanges[k] = new RawRgctxRange(Image.U32(e), Image.I32(e + 4), Image.I32(e + 8));
            }

            ulong rgctxs = W("rgctxs");
            module.Rgctxs = new RawRgctxEntry[rgctxCount];
            for (long k = 0; k < rgctxCount && rgctxs != 0; k++)
            {
                if (Version < MetaVersion.V27_2)
                {
                    ulong e = rgctxs + (ulong)k * 8;
                    module.Rgctxs[k] = new RawRgctxEntry((RgctxKind)Image.I32(e), Image.I32(e + 4), 0);
                }
                else
                {
                    ulong e = rgctxs + (ulong)k * 2 * ps;
                    var kind = (RgctxKind)Image.I32(e);
                    ulong data = Image.Ptr(e + ps);
                    int index = data != 0 && Image.IsMapped(data, 4) ? Image.I32(data) : -1;
                    uint encoded = kind == RgctxKind.Constrained && Image.IsMapped(data, 8) ? Image.U32(data + 4) : 0;
                    module.Rgctxs[k] = new RawRgctxEntry(kind, index, encoded);
                }
            }

            if (ml.Has("moduleInitializer")) module.ModuleInitializer = W("moduleInitializer");
            Modules[i] = module;
            ModulesByName[module.Name] = module;
        }
    }

    private void ReadMetadataRegistration(MetadataFile metadata)
    {
        WordLayout ml = WordLayout.MetadataRegistration(Version);
        ulong ps = (ulong)_ps;
        ulong mr = MetadataRegistrationVa;
        ulong W(string field) => Image.Ptr(mr + (ulong)ml.IndexOf(field) * ps);

        // Type table first: other records refer to types by address.
        ulong[] typePointers = ReadPointerArray(W("types"), (int)W("typesCount"));
        TableTypeCount = typePointers.Length;
        foreach (ulong va in typePointers) AddType(va);

        ulong[] instPointers = ReadPointerArray(W("genericInsts"), (int)W("genericInstsCount"));
        TableGenericInstCount = instPointers.Length;
        foreach (ulong va in instPointers) AddGenericInst(va);

        // Resolving links can append types and instantiations that are referenced but not registered, so run both
        // worklists to a fixed point.
        int nextType = 0, nextInst = 0;
        while (nextType < Types.Count || nextInst < GenericInsts.Count)
        {
            while (nextType < Types.Count) ResolveLinks(Types[nextType++]);
            while (nextInst < GenericInsts.Count) ResolveGenericInst(GenericInsts[nextInst++]);
        }

        int specCount = (int)W("methodSpecsCount");
        ulong specs = W("methodSpecs");
        MethodSpecs = new RawMethodSpec[specCount];
        for (int i = 0; i < specCount; i++)
        {
            ulong e = specs + (ulong)i * 12;
            MethodSpecs[i] = new RawMethodSpec(Image.I32(e), Image.I32(e + 4), Image.I32(e + 8));
        }

        int tableCount = (int)W("genericMethodTableCount");
        ulong table = W("genericMethodTable");
        bool adjustor = WordLayout.HasAdjustorThunks(Version);
        ulong entrySize = adjustor ? 16UL : 12UL;
        GenericMethodTable = new RawGenericMethodFunction[tableCount];
        for (int i = 0; i < tableCount; i++)
        {
            ulong e = table + (ulong)i * entrySize;
            GenericMethodTable[i] = new RawGenericMethodFunction(Image.I32(e), Image.I32(e + 4), Image.I32(e + 8),
                adjustor ? Image.I32(e + 12) : -1);
        }

        FieldOffsetPointers = ReadPointerArray(W("fieldOffsets"), (int)W("fieldOffsetsCount"));
        GenericClassPointers = ReadPointerArray(W("genericClasses"), (int)W("genericClassesCount"));

        ulong[] sizePointers = ReadPointerArray(W("typeDefinitionsSizes"), (int)W("typeDefinitionsSizesCount"));
        TypeSizes = new RawTypeSizes[sizePointers.Length];
        for (int i = 0; i < sizePointers.Length; i++)
        {
            ulong p = sizePointers[i];
            if (p != 0 && Image.IsMapped(p, 16))
                TypeSizes[i] = new RawTypeSizes(Image.U32(p), Image.I32(p + 4), Image.U32(p + 8), Image.U32(p + 12));
        }

        long usages = (long)W("metadataUsagesCount");
        if (usages > 0 && usages < 0x4000000 && W("metadataUsages") != 0)
            MetadataUsageSlots = ReadPointerArray(W("metadataUsages"), (int)usages);

        if (FieldOffsetPointers.Length != metadata.Types.Length)
            throw new RegistrationNotFoundException("Field offset table does not match the type definition count");
    }

    // ---- Il2CppType graph --------------------------------------------------------------------------------------

    private int AddType(ulong va)
    {
        if (_typeIndexByVa.TryGetValue(va, out int existing)) return existing;
        if (!Image.IsMapped(va, _ps + 4))
            throw new RegistrationNotFoundException($"Il2CppType at 0x{va:X} is out of range");
        ulong data = Image.Ptr(va);
        uint bits = Image.U32(va + (ulong)_ps);
        var t = new RawType
        {
            Va = va,
            Data = data,
            Attrs = (ushort)(bits & 0xFFFF),
            Type = (Il2CppTypeEnum)((bits >> 16) & 0xFF),
        };
        if (Version >= MetaVersion.V27_2)
        {
            t.NumMods = (int)((bits >> 24) & 0x1F);
            t.ByRef = ((bits >> 29) & 1) != 0;
            t.Pinned = ((bits >> 30) & 1) != 0;
        }
        else
        {
            t.NumMods = (int)((bits >> 24) & 0x3F);
            t.ByRef = ((bits >> 30) & 1) != 0;
            t.Pinned = (bits >> 31) != 0;
        }
        int index = Types.Count;
        Types.Add(t);
        _typeIndexByVa[va] = index;
        return index;
    }

    private int AddGenericInst(ulong va)
    {
        if (_genericInstIndexByVa.TryGetValue(va, out int existing)) return existing;
        int index = GenericInsts.Count;
        GenericInsts.Add(new RawGenericInst { Va = va });
        _genericInstIndexByVa[va] = index;
        return index;
    }

    private void ResolveGenericInst(RawGenericInst inst)
    {
        if (inst.TypeArgs.Length != 0 || !Image.IsMapped(inst.Va, 2 * _ps)) return;
        long argc = Image.NInt(inst.Va) & 0xFFFFFFFF;
        ulong argv = Image.Ptr(inst.Va + (ulong)_ps);
        if (argc <= 0 || argc > 64 || !Image.IsMapped(argv, (int)argc * _ps)) return;
        var args = new int[argc];
        for (int i = 0; i < argc; i++)
        {
            int index = AddType(Image.Ptr(argv + (ulong)(i * _ps)));
            args[i] = index;
        }
        inst.TypeArgs = args;
    }

    private void ResolveLinks(RawType t)
    {
        switch (t.Type)
        {
            // Built-in types also carry the index of their corlib type definition (System.Int32 and so on).
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
            case Il2CppTypeEnum.Class:
            case Il2CppTypeEnum.ValueType:
            case Il2CppTypeEnum.Var:
            case Il2CppTypeEnum.MVar:
                t.DefinitionIndex = (int)(uint)t.Data;
                break;
            case Il2CppTypeEnum.Ptr:
            case Il2CppTypeEnum.SzArray:
                if (t.ElementType < 0 && Image.IsMapped(t.Data, _ps + 4)) t.ElementType = AddType(t.Data);
                break;
            case Il2CppTypeEnum.Array:
                if (t.ElementType < 0 && Image.IsMapped(t.Data, 2 * _ps))
                {
                    ulong elem = Image.Ptr(t.Data);
                    if (Image.IsMapped(elem, _ps + 4)) t.ElementType = AddType(elem);
                    t.ArrayRank = Image.U8(t.Data + (ulong)_ps);
                }
                break;
            case Il2CppTypeEnum.GenericInst:
                if (t.GenericInst < 0 && Image.IsMapped(t.Data, 3 * _ps))
                {
                    ulong first = Image.Ptr(t.Data);
                    if (Version >= MetaVersion.V27_0)
                    {
                        // Points at the Il2CppType of the generic type definition.
                        if (Image.IsMapped(first, _ps + 4))
                            t.GenericTypeDefinition = (int)(uint)Image.Ptr(first);
                    }
                    else
                    {
                        t.GenericTypeDefinition = (int)(uint)first;
                    }
                    ulong classInst = Image.Ptr(t.Data + (ulong)_ps);
                    if (classInst != 0) t.GenericInst = AddGenericInst(classInst);
                }
                break;
        }
    }

    public int TypeIndexOf(ulong va) => _typeIndexByVa.TryGetValue(va, out int i) ? i : -1;

    /// <summary>Byte offset of a field within its object or static block, or -1 when unavailable.</summary>
    public int GetFieldOffset(int typeDefinitionIndex, int fieldIndexInType)
    {
        if ((uint)typeDefinitionIndex >= (uint)FieldOffsetPointers.Length) return -1;
        ulong p = FieldOffsetPointers[typeDefinitionIndex];
        if (p == 0) return -1;
        ulong va = p + (ulong)fieldIndexInType * 4;
        return Image.IsMapped(va, 4) ? Image.I32(va) : -1;
    }
}
