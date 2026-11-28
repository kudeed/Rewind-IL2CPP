# SinCos output effects

This independent runner checks the new `MethodPipeline` memory-effect rule for recognized direct `sincosf` / `sincos` calls. It calls the production `EscapeExtent`, `WritesOnly`, `ReadsOnly` and `WritesAndNothingElse` callbacks, then uses the existing `StackSplitting` pass. It does not run Unity, native recovery, the numeric/REV64/wide-array suites, or historical tests.

## Native defect

The original `AssetKits.ParticleImage.ParticleData::Simulate` method uses `sp+0x130` first for a 16-byte Quaternion and later for a completely overwritten 12-byte Vector3. At `0x6e4c730` it writes eight zero bytes; at `0x6e4c738` it writes the final float. `0x6e4c73c` calls `Quaternion.Internal_FromEulerRad(in Vector3)`. Its four-lane Quaternion result is correct. The old fourth component at `sp+0x13c` is not part of the new Vector3.

The final native `sincosf` call at `0x6e4ca30` writes a float through each of `sp+0x8c` and `sp+0x88`. The PLT at `0x7dd1610` is proven by the original ELF `.rela.plt` / `.dynsym` entry to import `sincosf`. Before this change, both helper pointers had an unknown extent and appeared to read/write everything above them, including the reused Quaternion/Vector3 storage. That false read joined the new three components to the old fourth component.

The diagnosis and native/code excerpts are frozen outside the source tree in `v9-rewind-quaternion-vector3-diagnosis`, rooted at `ROOT_CAUSE.json` SHA-256 `8a774b550fa4b59328dfda1c44e46d88c72ec514b4f9b4b2cb14da745b122d5c`. The same defect remains in the SIMD/memory branch's `native-after.log` SHA-256 `d1cca2ee5bec295dd8ebe29767e066ce81a98a0dda12db33e5f02a870748ac83`. No HFA, cast, game-specific type or RVA rule is added.

## Boundaries

The output extent and the write-only proof are separate claims:

- A recognized direct call with a complete, unique output-slot mapping has a 4-byte (`sincosf`) or 8-byte (`sincos`) extent for each output. ARM64 uses integer register slots 0/1 alongside `v0`; Win64 uses shared slots 1/2 (`rdx`/`r8`) alongside `xmm0`.
- `WritesOnly` is granted only when both output addresses share one identical SSA base and their bounded constant offsets prove that the byte ranges do not overlap. Different IR variables do not prove non-aliasing.
- Same, partially overlapping, or unproved output addresses retain conservative read/write effects. The actual native call remains unchanged. This is necessary because the existing splitter processes each call input separately: two overlapping write-only accesses could become different groups and redirect only one output pointer.
- Unclassified/unknown targets, indirect calls, intrinsics, non-output slots, inconsistent input/slot counts, missing/duplicate output slots and non-pointer-width output inputs do not acquire the new precision.
- `REWIND_NO_HELPER_EXTENTS` disables both claims. `ReadsOnly` and `WritesAndNothingElse` remain false for these outputs. Unused output values do not authorize deleting a native call or its other effects.

No other runtime helper changes. In particular, this patch does not generalize the pre-existing `Modf` position rule or rewrite `StackSplitting`.

## Groups

| Group | Checks |
|---|---|
| `effects` | Both ABIs, float/double extents, adjacent disjoint outputs, reordered input vectors, floating argument rejection and call preservation |
| `stack` | The actual false-lifetime counterexample with the old unbounded callbacks, then separation with production precise effects and identical byte observations |
| `cfg` | Both branch paths; a real 16-byte join read and a partial overwrite prevent unsafe separation |
| `aliases` | Same/partially overlapping outputs keep their addresses and byte results; distinct SSA pointer variables are not presumed disjoint; unused outputs keep the call |
| `reject` | Unknown, indirect, intrinsic and malformed mappings, including negative/past-end input indices |
| `disabled` | A fresh child process verifies the static `REWIND_NO_HELPER_EXTENTS` gate before type initialization |

The fixture initializes every dependency used by these production callbacks: real ABI objects, the image/layout context, both method lookup tables, the helper registry and the empty-target resolution cache. It does not enter `HirBuilder`, normalization or lifting, so it neither constructs a partial HIR recovery context nor loads an ELF. The memory oracle interprets only literal stores, fixture consumers and opaque helper output patterns; it does not substitute `System.Math` for native `sincos` accuracy or output-write order.

## Build and run

The integrator builds against the one freshly built CLI output:

```sh
dotnet build tests/Rewind.Analysis.SinCosEffects.Tests/Rewind.Analysis.SinCosEffects.Tests.csproj -c Release --no-restore -m:1 -p:RewindBinaryDir=/absolute/path/to/cli/bin/Release/net10.0
dotnet tests/Rewind.Analysis.SinCosEffects.Tests/bin/Release/net10.0/Rewind.Analysis.SinCosEffects.Tests.dll --report /absolute/evidence/SINCOS_RESULTS.json --journal /absolute/evidence/SINCOS_GROUPS.jsonl
```

Each completed group is printed and appended to the JSONL journal immediately. A failure does not prevent other selected groups from reporting. The summary is per invocation; the journal retains prior passed groups across a retry. Retry only the affected group:

```sh
dotnet tests/Rewind.Analysis.SinCosEffects.Tests/bin/Release/net10.0/Rewind.Analysis.SinCosEffects.Tests.dll --group aliases --report /absolute/evidence/SINCOS_ALIAS_RETRY.json --journal /absolute/evidence/SINCOS_GROUPS.jsonl
```

After the new suite passes, the integrator recovers only `AssetKits.ParticleImage.ParticleData::Simulate` once, using the already archived pre-change output for comparison. The native check must verify a Vector3 argument at `Internal_FromEulerRad`, preserved Quaternion/HFA returns, and no new method problems. This runner does not perform that recovery or claim it has passed.
