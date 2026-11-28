using System.Security.Cryptography;
using Mono.Cecil;

namespace Rewind.Output;

public sealed record FrameworkAssemblyEvidence(string Path, string Sha256, string Identity);
public sealed record FrameworkTypeEvidence(string Name, string Assembly, string Path, uint Token,
    IReadOnlyList<string> Forwarders);
public sealed record FrameworkReferenceDecision(string OriginalScope, IReadOnlyList<string> Types,
    string Status, string? TargetScope, IReadOnlyList<FrameworkTypeEvidence> Evidence);
public sealed record FrameworkReferenceAdaptation(string Assembly, int Groups, int OutsideProfile,
    int AlreadyResolvable, int ChangedTypeReferences, IReadOnlyList<FrameworkReferenceDecision> Decisions);

/// <summary>
/// Adapts references in a COPY of a recovered assembly to an explicitly supplied framework reference profile.
/// This repairs type ownership lost when IL2CPP folded framework types into its core library. It does not
/// recover methods, provide runtime implementations, change visibility, or guess ownership from a namespace.
/// Original scopes that already resolve are retained. A missing type must resolve uniquely, publicly, and
/// with its complete declaring-type chain in the supplied profile before its scope can change.
/// </summary>
public sealed class TargetFrameworkReferenceAdapter : IDisposable
{
    private sealed class ProfileAssembly
    {
        public required AssemblyDefinition Assembly { get; init; }
        public required FrameworkAssemblyEvidence Evidence { get; init; }
        public required Dictionary<string, TypeDefinition> Types { get; init; }
        public required Dictionary<string, ExportedType> Exports { get; init; }
    }

    private sealed record ResolvedType(ProfileAssembly Owner, TypeDefinition Type, string[] Forwarders);
    private readonly Dictionary<string, ProfileAssembly> _profile = new(StringComparer.OrdinalIgnoreCase);
    public IReadOnlyList<FrameworkAssemblyEvidence> Profile => _profile.Values.Select(x => x.Evidence).ToArray();

    public TargetFrameworkReferenceAdapter(IEnumerable<string> referenceAssemblyPaths)
    {
        try
        {
            foreach (string path in referenceAssemblyPaths.Select(System.IO.Path.GetFullPath)
                         .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal))
            {
                // Read only the supplied files. No package acquisition or search through the running CLR.
                var assembly = AssemblyDefinition.ReadAssembly(path, new ReaderParameters
                {
                    InMemory = true, ReadingMode = ReadingMode.Deferred, ReadSymbols = false,
                });
                if (_profile.ContainsKey(assembly.Name.Name))
                {
                    assembly.Dispose();
                    throw new ArgumentException($"Ambiguous framework assembly name: {assembly.Name.Name}");
                }
                _profile.Add(assembly.Name.Name, new ProfileAssembly
                {
                    Assembly = assembly,
                    Evidence = new(path, Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path))).ToLowerInvariant(),
                        assembly.Name.FullName),
                    Types = assembly.MainModule.GetTypes().ToDictionary(t => t.FullName, StringComparer.Ordinal),
                    Exports = assembly.MainModule.ExportedTypes.ToDictionary(t => t.FullName, StringComparer.Ordinal),
                });
            }
            if (_profile.Count == 0) throw new ArgumentException("A real target reference profile is required.");
        }
        catch { Dispose(); throw; }
    }

    private static bool IsPublic(TypeDefinition type) => type.DeclaringType is null
        ? type.IsPublic : type.IsNestedPublic && IsPublic(type.DeclaringType);

    private static bool IdentityMatches(AssemblyNameReference reference, AssemblyNameDefinition target,
        bool permitUnsignedRecoveredReference)
    {
        if (!StringComparer.OrdinalIgnoreCase.Equals(reference.Name, target.Name) || reference.Version != target.Version ||
            !StringComparer.OrdinalIgnoreCase.Equals(reference.Culture ?? "", target.Culture ?? "")) return false;
        byte[] expected = reference.PublicKeyToken ?? [];
        byte[] actual = target.PublicKeyToken ?? [];
        // Old recovered assemblies have no key. This exception is only for the original scope, never a real
        // framework forwarder; the destination always receives the target's complete identity.
        return (permitUnsignedRecoveredReference && expected.Length == 0) || expected.AsSpan().SequenceEqual(actual);
    }

    private ResolvedType? Resolve(ProfileAssembly assembly, string name, HashSet<string>? visited = null,
        List<string>? hops = null)
    {
        visited ??= new(StringComparer.Ordinal);
        hops ??= [];
        if (!visited.Add(assembly.Assembly.Name.FullName + "::" + name)) return null;
        if (assembly.Types.TryGetValue(name, out TypeDefinition? definition))
            return new(assembly, definition, hops.ToArray());
        if (!assembly.Exports.TryGetValue(name, out ExportedType? exported)) return null;
        ExportedType root = exported;
        while (root.DeclaringType is not null) root = root.DeclaringType;
        if (!root.IsForwarder || root.Scope is not AssemblyNameReference target ||
            !_profile.TryGetValue(target.Name, out ProfileAssembly? next) ||
            !IdentityMatches(target, next.Assembly.Name, permitUnsignedRecoveredReference: false)) return null;
        hops.Add(assembly.Assembly.Name.FullName + "::" + name + " -> " + target.FullName);
        return Resolve(next, name, visited, hops);
    }

    private IEnumerable<ResolvedType> Candidates(string name) => _profile.Values
        .Select(a => Resolve(a, name)).Where(r => r is not null && IsPublic(r.Type)).Cast<ResolvedType>()
        .DistinctBy(r => r.Owner.Assembly.Name.FullName, StringComparer.Ordinal);

    private static TypeReference Root(TypeReference type)
    {
        while (type.DeclaringType is not null) type = type.DeclaringType;
        return type;
    }

    private static IEnumerable<string> TypeChain(TypeReference type)
    {
        for (TypeReference? current = type; current is not null; current = current.DeclaringType)
            yield return current.FullName;
    }

    private static AssemblyNameReference TargetScope(ModuleDefinition module, AssemblyNameDefinition target)
    {
        AssemblyNameReference? reference = module.AssemblyReferences.FirstOrDefault(x => x.FullName == target.FullName);
        if (reference is not null) return reference;
        reference = new(target.Name, target.Version)
        {
            Culture = target.Culture,
            PublicKeyToken = (target.PublicKeyToken ?? []).ToArray(),
            IsRetargetable = target.IsRetargetable,
        };
        module.AssemblyReferences.Add(reference);
        return reference;
    }

    /// <summary>
    /// The module must have been read from emitted metadata, including an in-memory emission. Cecil does not
    /// expose all imported TypeRef rows through GetTypeReferences before an emission. Callers own the copy and
    /// must persist this report with it; the report never establishes runtime or gameplay correctness.
    /// </summary>
    public FrameworkReferenceAdaptation Adapt(ModuleDefinition module)
    {
        var decisions = new List<FrameworkReferenceDecision>();
        int outside = 0, already = 0, changed = 0;
        // Snapshot before changes: nested TypeRef.Scope can delegate to its declaring type's scope.
        var groups = module.GetTypeReferences().Where(t => t.Scope is AssemblyNameReference)
            .GroupBy(t => (((AssemblyNameReference)t.Scope).FullName, Root(t).FullName)).ToArray();
        foreach (var group in groups)
        {
            TypeReference[] references = group.ToArray();
            var original = (AssemblyNameReference)references[0].Scope;
            string[] names = references.SelectMany(TypeChain).Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal).ToArray();
            if (!_profile.TryGetValue(original.Name, out ProfileAssembly? source)) { outside++; continue; }
            if (!IdentityMatches(original, source.Assembly.Name, permitUnsignedRecoveredReference: true))
            {
                decisions.Add(new(original.FullName, names, "source_identity_mismatch", null, []));
                continue;
            }
            ResolvedType?[] existing = names.Select(n => Resolve(source, n)).ToArray();
            if (existing.All(r => r is not null)) { already++; continue; }
            // A valid enclosing type with a missing nested type is not permission to move that whole family.
            if (existing.Any(r => r is not null))
            {
                decisions.Add(new(original.FullName, names, "partially_resolvable_family", null, []));
                continue;
            }
            if (names.Any(source.Exports.ContainsKey))
            {
                // An explicit but incomplete forwarding contract is evidence of a missing profile file,
                // not permission to substitute another same-named definition.
                decisions.Add(new(original.FullName, names, "unresolved_forwarder", null, []));
                continue;
            }
            ResolvedType[][] candidates = names.Select(n => Candidates(n).ToArray()).ToArray();
            var identities = candidates[0].Select(r => r.Owner.Assembly.Name.FullName).ToHashSet(StringComparer.Ordinal);
            foreach (ResolvedType[] family in candidates.Skip(1))
                identities.IntersectWith(family.Select(r => r.Owner.Assembly.Name.FullName));
            if (identities.Count != 1)
            {
                decisions.Add(new(original.FullName, names, identities.Count == 0 ? "unresolved" : "ambiguous", null,
                    candidates.SelectMany(c => c).Select(Evidence).ToArray()));
                continue;
            }
            string identity = identities.Single();
            ResolvedType[] selected = candidates.Select(c => c.Single(r => r.Owner.Assembly.Name.FullName == identity)).ToArray();
            AssemblyNameReference target = TargetScope(module, selected[0].Owner.Assembly.Name);
            foreach (TypeReference root in references.Select(Root).Distinct()) root.Scope = target;
            changed += references.Length;
            decisions.Add(new(original.FullName, names, "retargeted", target.FullName, selected.Select(Evidence).ToArray()));
        }
        return new(module.Assembly.Name.FullName, groups.Length, outside, already, changed, decisions);
    }

    private static FrameworkTypeEvidence Evidence(ResolvedType resolved) => new(resolved.Type.FullName,
        resolved.Owner.Assembly.Name.FullName, resolved.Owner.Evidence.Path, resolved.Type.MetadataToken.ToUInt32(),
        resolved.Forwarders);

    public void Dispose()
    {
        foreach (ProfileAssembly assembly in _profile.Values) assembly.Assembly.Dispose();
        _profile.Clear();
    }
}
