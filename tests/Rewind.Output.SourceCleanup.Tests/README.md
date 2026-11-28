# SourceCleanup regression scope (PAP v8)

This project links the production `SourceCleanup.cs` directly. It has no NuGet package dependencies and references the C# compiler shipped in the selected .NET SDK. It compiles emitted C# 9 fixtures in memory and executes the operator and optional-hook cases. It is an emitter regression test, not a gameplay test or a replacement gameplay implementation.

Run serially with the other mj5 .NET work:

```bash
dotnet run --project tests/Rewind.Output.SourceCleanup.Tests/SourceCleanupRegression.csproj -c Release -p:UseSharedCompilation=false
```

The project defaults to workstation GC. The coordinator should keep the existing 1-core/512 MiB process budget and capture stdout/exit code. No result is claimed until the command has actually run.

## Evidence and decisions

- `evidence.json` retains the exact 40 native bytes at PAP `SerializableSystemType.op_Equality`, token `0x06000987`, RVA `0x3E3EEC8`. The branch sequence compares object references, accepts equal references (including null/null), rejects a single null, then tail-calls `Equals(SerializableSystemType)` at `0x3E3EE7C`.
- The retained type metadata has six methods and no `op_Inequality`. The C# compiler requires a paired operator. The generated `!=` is explicitly a source compatibility member defined as the complement of the evidenced equality; it is not counted as a newly recovered native method.
- The old R4 helper made two distinct wrappers around the same Type satisfy both `==` and `!=`. Explicit `ReferenceEquals` checks inside `==` preserve the native branch semantics and avoid recursion when `!=` calls `==`.
- The native GetHashCode method is also absent. The existing source compatibility hash uses SystemType so value-equal wrappers hash equally; this pass changes its explanatory comment only.
- The inherited-member `new` rule matched names anywhere in declarations, including constructor names and member types. It is removed; existing explicit `new` is preserved. The specific event-field/camera repairs now match `internal` after accessibility widening.
- Optional IronSource subscriptions, unsubscriptions and callback bodies are preserved under `PAP_ENABLE_AD_SDK`, with source comments explaining the hooks. Application pause/resume code remains outside those guards. This preserves opt-in behavior and removes the SDK type dependency from default gameplay builds.
- Pre-cleanup capture of three existing recovered types proves that the `_list` assignment regex truncated a legal nested cast at its first `)`. Embedded assignments are now protected with balanced parentheses, skipping quoted text/comments, and restored unchanged after legacy cleanup. Their stores and values are retained. This repairs the tool's syntax damage without claiming that the recovered field types or exception slots are correct.

## Covered cases

- Sixteen equality/inequality pairs: null, identical reference, different wrappers around the same System.Type, and different System.Type values; equal-object hash consistency; R4 helper migration; unknown equality body rejection; repeat-pass stability.
- Constructors and unrelated members are not assigned `new`; explicit original hiding is retained; event/camera rules work after `private` becomes `internal`.
- Default build compiles without any ad SDK types; opt-in build preserves callback state changes and subscribe/unsubscribe direction; pause callbacks remain available in both; guarded source remains stable on a second pass.
- A nested embedded `_list` assignment preserves its result, field store, quoted closing parenthesis, and single evaluation of a call. Optional `--captures <capture-directory>` verifies all six real captured catch expressions across the three affected types.

## Existing recovery risks outside this patch

The remainder of SourceCleanup predates this patch and still contains broad lossy rewrites: replacing BCL/span/enumerator fields with defaults, dropping writes, converting generic casts to guessed receivers, replacing internal geometry tests with `true`, and replacing Span with arrays. These are **unresolved semantic recovery risks**, not accepted gameplay equivalence. This scoped patch does not add such replacements and does not certify existing ones. A compilable source gate cannot close DFS or behavior/visual acceptance while those paths remain unresolved.

The former four externally normalized catch assignments are part of six captured expressions: EconomyController has four (two `list` plus two `list2`), and LevelEndScreenView / AbstractChildServiceController each have one. The `list2` hard-coded replacement had concealed two instances. A bounded capture using the existing Rewind/ILSpy DLLs, without a native lift, proved that the raw decompiler expression was `(Exception)(object)(enumerator._list = (List<T>)(object)list)`. The old regex consumed only through `(List<T>)` and injected `null)`, leaving malformed casts behind. This pass preserves the entire original assignment and removes that truncation and its hard-coded `list2` patch, so an external `ex = list` semantic guess is no longer needed for these syntax errors.

The captured **recovered** IL still writes an Exception local directly into a `List<T>.Enumerator._list` field and later uses that slot for exception propagation. That is an unresolved IR typing/slot-lifetime problem, not verified original managed IL or native catch semantics. The new cleanup intentionally keeps the assignment and any resulting type/accessibility diagnostic visible; it does not substitute null/default, discard the field store, or claim a completed DFS method. `catch-evidence.json` records input/output identities and the evidence boundary. The native recovery phase must still separate the exception storage lifetime from the reused enumerator slot.
