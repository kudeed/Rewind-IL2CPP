# Value snapshot regressions

This project exercises the computed-value materialization boundary and exact whole-struct copy recovery using small synthetic HIR fixtures. It references already-built Rewind binaries, has no package dependency, and does not load a game or execute a native lift.

Build the CLI first, then run:

```sh
DOTNET_PROCESSOR_COUNT=1 DOTNET_GCHeapHardLimit=0x20000000 dotnet run \
  --project tests/Rewind.Analysis.ValueSnapshots.Tests \
  --configuration Release --no-restore
```

For an isolated binary snapshot, supply `-p:RewindBinaryDir=/absolute/path/to/binaries`. A first run may need a package-free restore of this test project. The test runner prints a JSON receipt and exits nonzero on any failed assertion. It neither builds Rewind through project references nor runs a full source export.

## Evidence

Two original PAP methods exhibit a load-before-clear pattern in the original ARM64 binary:

| Method | Metadata token | Native RVA | Native value preservation |
| --- | --- | --- | --- |
| `CoreScenesHandler/<LoadAndActivateScene>d__13::MoveNext` | `06008B86` | `0419F1B0` | `0419F260` loads the 16-byte awaiter, `0419F268` clears the field, `0419F270` stores the loaded value. `0419F278` similarly loads 32 bytes before `0419F280` clears them and `0419F288` stores the old registers. |
| `GameEndPodium/<LoadSkin>d__23::MoveNext` | `06000BD6` | `04069278` | `04069380` loads 16 bytes before `04069388` clears them. The 40-byte generic awaiter is loaded at `04069398`/`0406939C` before the clears at `040693A0`/`040693B0`. |

The input inventory records ELF SHA-256 `cf0fe59687988793400852978382bef8626a29326f53d2ccedb16b4db79a2bec`. The ELF program headers were checked when extracting these method ranges; the executable load segment maps these RVAs to file offsets by subtracting `0x4000`.

The existing recovered `Assembly-CSharp.dll` has SHA-256 `c483fc0344d3444439094addf3ac52e411664f2eba093e39aeb7db8603c3da96`. Reading it with Mono.Cecil confirms that the ordering error already exists in IL, before C# decompilation and source cleanup:

- CoreScenesHandler: `IL_0067` clears `<>u__2`; `IL_0074` rereads it for the local awaiter.
- GameEndPodium: `IL_0054` clears `<>u__2`; `IL_0061` rereads it. The generic result is cleared at `IL_00D4`, then `IL_0132` reads its `Version`.

The capture receipt and full method IL are on mj8 under `/home/admin/unity/validation/pap-v8-batch-20261128/tool-tests/awaiter-evidence/RECOVERED_IL.jsonl`. The input hash is checked again after capture. This evidence identifies recovery defects; it is not a claim that either complete PAP method is runtime-verified.

## Regression coverage

- 16-, 32-, and 40-byte layouts, including reference identity, token, scene handle, release flag, operation, handle version, location name, and padding.
- Every native word's actual leaf values survive a later clear; the original storage still becomes default.
- Same-block, unchanged field values can become a whole-struct copy, including an exact constructed generic type.
- Whole-source and nested-field changes, unknown calls, possibly aliasing pointer writes, address-taken locals, mutated struct locals, non-dominating definitions, and value-changing conversions prevent unsafe rereads.
- Getter and destination expressions retain evaluation counts. A property-shaped name alone does not establish purity.

The interpreter handles only the HIR operations used by these fixtures and compares observable values/call counts. It is not an SDK substitute. The tests deliberately do not claim full pipeline, emitted-game runtime, or public-API reconstruction coverage. A new native lift of selected real methods is the next integration check after this bounded correction.
