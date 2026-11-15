using Rewind.Metadata;

namespace Rewind.Runtime;

/// <summary>
/// Field order of the registration structs IL2CPP emits into the binary. Every field is one pointer-sized word
/// (32-bit counts are padded by alignment), so a layout is just an ordered list of names.
/// </summary>
public sealed class WordLayout
{
    private readonly Dictionary<string, int> _index = new(StringComparer.Ordinal);

    public IReadOnlyList<string> Fields { get; }
    public int WordCount => Fields.Count;

    public WordLayout(IEnumerable<string> fields)
    {
        Fields = fields.ToList();
        for (int i = 0; i < Fields.Count; i++) _index[Fields[i]] = i;
    }

    public bool Has(string field) => _index.ContainsKey(field);
    public int IndexOf(string field) => _index.TryGetValue(field, out int i) ? i : -1;

    public static bool HasAdjustorThunks(int v) => v >= MetaVersion.V24_5 && v != MetaVersion.V27_0;

    public static WordLayout CodeRegistration(int v)
    {
        var f = new List<string>();
        if (v <= MetaVersion.V24_15) f.AddRange(["methodPointersCount", "methodPointers"]);
        f.AddRange(["reversePInvokeWrapperCount", "reversePInvokeWrappers", "genericMethodPointersCount", "genericMethodPointers"]);
        if (HasAdjustorThunks(v)) f.Add("genericAdjustorThunks");
        f.AddRange(["invokerPointersCount", "invokerPointers"]);
        if (v <= MetaVersion.V24_5) f.AddRange(["customAttributeCount", "customAttributeGenerators"]);
        f.AddRange(["unresolvedVirtualCallCount", "unresolvedVirtualCallPointers"]);
        if (v >= MetaVersion.V29_1 && v != MetaVersion.V31_0)
            f.AddRange(["unresolvedInstanceCallPointers", "unresolvedStaticCallPointers"]);
        f.AddRange(["interopDataCount", "interopData"]);
        if (v >= MetaVersion.V24_2)
        {
            if (v >= MetaVersion.V24_3) f.AddRange(["windowsRuntimeFactoryCount", "windowsRuntimeFactoryTable"]);
            f.AddRange(["codeGenModulesCount", "codeGenModules"]);
        }
        return new WordLayout(f);
    }

    public static WordLayout MetadataRegistration(int v) => new(
    [
        "genericClassesCount", "genericClasses", "genericInstsCount", "genericInsts",
        "genericMethodTableCount", "genericMethodTable", "typesCount", "types",
        "methodSpecsCount", "methodSpecs", "fieldOffsetsCount", "fieldOffsets",
        "typeDefinitionsSizesCount", "typeDefinitionsSizes", "metadataUsagesCount", "metadataUsages",
    ]);

    public static WordLayout CodeGenModule(int v)
    {
        var f = new List<string> { "moduleName", "methodPointerCount", "methodPointers" };
        if (HasAdjustorThunks(v)) f.AddRange(["adjustorThunkCount", "adjustorThunks"]);
        f.AddRange(
        [
            "invokerIndices", "reversePInvokeWrapperCount", "reversePInvokeWrapperIndices",
            "rgctxRangesCount", "rgctxRanges", "rgctxsCount", "rgctxs", "debuggerMetadata",
        ]);
        if (v >= MetaVersion.V27_0)
        {
            if (v < MetaVersion.V29_0) f.Add("customAttributeCacheGenerator");
            f.AddRange(["moduleInitializer", "staticConstructorTypeIndices", "metadataRegistration", "codeRegistration"]);
        }
        return new WordLayout(f);
    }
}
