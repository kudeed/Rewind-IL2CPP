# CarEvolve recovery branch

This branch preserves the recovery changes used on the pinned Unity 6000.3.11f1 ARM64 CarEvolve input, on top of upstream experimental commit `ce314249dc6a3fddb67415f9fc8b963d5965253a`. It contains the complete 276-file SDK11 source/build/signature/test snapshot and two subsequently verified upstream changes.

The additional upstream changes are `c3bf71a4a7530778507c50f953dff6f8116c7820` (remove unused pure value markers, preserving effects and possible exceptions) and `e08db8d06c6d0bbe7fd93984b0afa296d27e38ad` (preserve typed pointer arithmetic while retaining its diagnostic). Local ARM64, metadata, constructor, receiver, struct-copy, emission and source-projection fixes remain present.

The final upstream commit's change from a raw-constructor gap to a note is deliberately not adopted. Raw allocation followed by a constructor call remains an explicit recovery gap until valid C# can be produced for this source-reconstruction workflow.

## Validation

- CLI and affected tests are built with .NET 10, with zero compiler warnings and errors required by the validation script.
- SDK11 baseline: twelve regression suites accepted; 4,472 SIMD output-bit comparisons against Unicorn; 37,224 packed-struct bit cases and 24 invalid-layout cases; receiver proof with two positive and fifteen negative cases.
- The two new upstream changes passed EmitterNumericLocalSmoke and FsmConstructionSmoke, plus 37 assertions covering unused markers, used markers, effects, exceptions and unrelated gaps.
- Full original dependency recovery: 27 type trees, 828 declarations, 827 native bodies and one preserved abstract declaration. Across 6,293 emitted assembly methods, 6,292 normalized bodies are unchanged from SDK11. Only previously rejected method 26690 changed. All 794 previously clean declarations and all unselected bodies remain unchanged; type, field and method contracts remain unchanged.
- The selected recovery queue still contains 32 rejected methods. This branch is an experimental recovery tool, not a declaration that the game or every recovery path is complete.

## Build and run

```sh
dotnet build src/Rewind.Cli/Rewind.Cli.csproj -c Release -nodeReuse:false -p:UseSharedCompilation=false
dotnet build tests/UpstreamValuePuritySmoke/UpstreamValuePuritySmoke.csproj -c Release -nodeReuse:false -p:UseSharedCompilation=false
dotnet tests/UpstreamValuePuritySmoke/bin/Release/net10.0/FsmConstructionSmoke.dll
```

The purity test uses the existing FsmConstructionSmoke friend-assembly identity to exercise internal recovery predicates. Its project and output are isolated from the existing FsmConstructionSmoke project.

The other smoke projects remain under `tests/`; tests requiring original native input must receive the matching library and metadata. No game binary, metadata dump, Unity project, save, generated build output or credentials are included.

## Known work remaining

The 32-method queue includes native stack lifetime/copy reconstruction, subtype receivers, multidimensional/generic array access, enumerator lifetime, metadata initialization and exception-region reconstruction. Advertising, analytics, payment and platform SDKs that the game does not need for offline play may be removed rather than reconstructed; engine and gameplay dependencies still require their original logic.

A separate confirmed ARM64 helper-discovery defect remains: the current exception-stub heuristic can read beyond a function boundary and misclassify an index-out-of-range thrower as an overflow thrower. Its original helper at ELF address `0x2341c40` calls the index-out-of-range path; adjacent `0x2341c48` belongs to the overflow factory. This semantic defect is not represented by the 34-method queue and is not claimed fixed here.

## Successful type-test receiver recovery

The receiver cast is restored only on paths dominated by a successful `isinst != null` edge, for an unchanged argument with metadata-matching type. Bypasses, failed paths, merges with failed paths, argument writes/address escapes, locals, unrelated/generic owners and exception regions do not qualify. The original test, object, call arguments and evaluation order stay in place.

Four positive and fifteen negative cases pass. Car.CopyWaterCollider now has all eleven derived receiver calls reconstructed, emits successfully and has no recovery or receiver-type gaps. The complete original batch changes only this method; 6,292 other assembly bodies, all 794 previously clean declarations and all metadata contracts remain unchanged. The selected queue is now 33.

```sh
dotnet build tests/TypeTestReceiverSmoke/TypeTestReceiverSmoke.csproj -c Release -nodeReuse:false -p:UseSharedCompilation=false
dotnet tests/TypeTestReceiverSmoke/bin/Release/net10.0/FsmConstructionSmoke.dll ORIGINAL_SO ORIGINAL_METADATA signatures FRESH_OUTPUT_DIRECTORY
```

## Conditional constructor overload recovery

Two branches may choose different constructors of the exact allocated class. A captured pure scalar condition selects one new expression at the original allocation; exactly one object is allocated and only the selected constructor runs. Constructor arguments are unescaped scalar values. Reading these values before allocation cannot observe a static initializer, so type initialization and constructor effects remain at the new expression. Finalizers, generic/ambiguous classes, effects before construction, aliases, early publication, extra predecessors and exception scopes remain rejected. Existing same-constructor rules retain their original initializer restrictions.

Two positive and eight negative cases pass, including the original System.Random metadata with its static constructor. TrafficPopulation.Start now preserves the seed-zero/default and explicit-seed overloads in valid emitted C#. Across all 6,293 assembly methods, only this formerly rejected body changes; all 795 previously clean declarations remain unchanged. The selected queue is now 32.

```sh
dotnet build tests/BranchOverloadSmoke/BranchOverloadSmoke.csproj -c Release -nodeReuse:false -p:UseSharedCompilation=false
dotnet tests/BranchOverloadSmoke/bin/Release/net10.0/FsmConstructionSmoke.dll ORIGINAL_SO ORIGINAL_METADATA signatures FRESH_OUTPUT_DIRECTORY
```

## Bounded lookup tables and partial struct tails

The selected 27-type queue is now 26 rejected methods (native19), down from 32 at native18. Six formerly rejected methods recover cleanly: Car.FixedStep, TrafficCar.OnDrawGizmosSelected, DiagonalSlicedUIButtonImage.AddRadialCorner and FindQuadCorner, UpgradeUI.EnsureReferences, and UnderwaterFishShoals.BuildMeshes. ModifyGeneratedMesh retains one explicit array-cursor gap.

Table expansion now proves zero-extended predicate domains, exact unsigned mask domains, and zero-based unit-step loops with a checked constant termination value. It preserves the existing immutable table reader and raw scalar bits. Metadata slot choices admit up to 32 predecessors, with every leaf still required to resolve through the original metadata. Struct-tail copies require a complete public numeric field cover and exact nonoverlapping stack slots; unknown layouts, gaps, private fields, readonly fields and partial overlaps remain rejected. Public Color32 bytes cover its private numeric union alias exactly.

The full 6,293-method comparison changed eight formerly rejected bodies; 6,285 bodies and all 796 previously clean declarations remain identical. Original type, field and method contracts are unchanged. This does not establish scene wiring or whole-game completion; the previously documented exception-helper boundary defect remains open.

```sh
dotnet build tests/BoundedTablesAndStructTailsSmoke -c Release -nodeReuse:false -p:UseSharedCompilation=false
dotnet tests/BoundedTablesAndStructTailsSmoke/bin/Release/net10.0/FsmConstructionSmoke.dll ORIGINAL_SO ORIGINAL_METADATA signatures FRESH_OUTPUT_DIRECTORY
```
