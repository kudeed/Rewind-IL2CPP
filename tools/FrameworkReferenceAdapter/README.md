# Explicit target framework reference adaptation

This tool repairs a specific IL2CPP export mismatch: a recovered reference names a type in the native core
library, while the selected Unity compiler framework defines it in a different assembly. It uses real
TypeDef rows and complete forwarder chains in an explicit profile, not a namespace replacement table.

It creates **diagnostic reference copies only**. It never fills missing method bodies, changes access flags,
or proves runtime behavior. Original input DLLs are opened read-only and re-hashed after processing.
Existing resolvable scopes, SDK scopes outside the explicit framework profile, ambiguous definitions,
incomplete forwarders, and identity mismatches are retained and reported. An altered copy must retain an
identical typed method-instruction fingerprint across metadata serialization.

The target is .NET 9 to allow running independently of the main Rewind build. It links the shared
`src/Rewind.Output/TargetFrameworkReferenceAdapter.cs` API and uses Rewind's existing Mono.Cecil 0.11.6 dependency.

```bash
dotnet build tools/FrameworkReferenceAdapter/FrameworkReferenceAdapter.csproj -c Release
dotnet tools/FrameworkReferenceAdapter/bin/Release/net9.0/FrameworkReferenceAdapter.dll \
  --self-test /absolute/new-test-directory
dotnet tools/FrameworkReferenceAdapter/bin/Release/net9.0/FrameworkReferenceAdapter.dll \
  --references /absolute/compile/Assembly-CSharp/REFERENCES.json \
  --output /absolute/new-reference-copy-directory
```

The manifest is the existing preflight reference map. `Unity_framework_reference` entries define the entire
explicit target profile; only `metadata_only_reference` entries are eligible for copied adaptation.
Authentic signed SDK implementations are refused even if accidentally misclassified.

For an offline build, pass `-p:CecilAssemblyPath=/absolute/verified/Mono.Cecil.dll` to use an existing
Mono.Cecil 0.11.6 binary instead of the package reference. The default package behavior is unchanged.
Keep `DOTNET_CLI_HOME`, `NUGET_PACKAGES` and temporary outputs within the selected work area. On hosts
without ICU, set `DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1` for both the SDK and tool process; this metadata
operation uses ordinal names and culture-invariant instruction fingerprints.

Outputs:

- `REFERENCE_MAP.json`: original mapping with only proven reference copies replaced.
- `ADAPTATION_RECEIPT.json`: profile hashes and full identities, source hashes, exact TypeDef tokens,
  forwarding evidence, unresolved/ambiguous cases, and method instruction fingerprints.
- `assemblies/`: only assemblies with proven scope changes.

The API operates on a module read back from emitted metadata, either from a file or an in-memory emission.
This is deliberate: Mono.Cecil does not enumerate all imported TypeRef rows until metadata has been emitted.
It does not silently change `AssemblyEmitter.Write` or any original native recovery evidence.
