# ARM64 numeric regression entry point

This independent executable targets the numeric defects proven by the original ParticleImage / Noise ARM64 bodies. It does not invoke the existing InlineTemplates or ValueSnapshots suites, build Unity, export a game, or modify project assets.

## Build and run

The integration owner builds this project against the already built candidate Rewind binaries. The test author does not build or run it separately.

```sh
dotnet build tests/Rewind.Analysis.Arm64Numeric.Tests/Rewind.Analysis.Arm64Numeric.Tests.csproj -c Release -p:RewindBinaryDir=/absolute/path/to/src/Rewind.Lab/bin/Release/net10.0 -p:UseSharedCompilation=false -m:1
dotnet tests/Rewind.Analysis.Arm64Numeric.Tests/bin/Release/net10.0/Rewind.Analysis.Arm64Numeric.Tests.dll --report /absolute/path/to/numeric-results.json
```

There are no NuGet test framework dependencies. The executable references `Rewind.Analysis.dll` and `Rewind.Core.dll` from `RewindBinaryDir`. Its report records the actual loaded analysis DLL hash, assertion count, passed groups and failures; the exit code is nonzero on any failed group.

## Targeted coverage

| Area | Checked behavior |
| --- | --- |
| Fixed-point GPR SCVTF / UCVTF | Supported combinations: signed W/X to F32/F64, unsigned W to F32/F64, unsigned X to F64; ordinary conversion and fractional bits 1 through boundary 32/64; exact `64-scale` decoding; source and destination register fields; 32-bit source truncation and scalar upper-lane clearing. Original words `1E028500` and `1E0286A0` are explicit fixtures. |
| Invalid / unsupported encodings | Reserved ptype 2; W-source scale below 32; half precision must be rejected or reported unsupported without producing a fake destination value. New fixed unsigned X to F32 explicitly remains unsupported. |
| FCMLT zero | 2S, 4S, 2D, S and D masks; all-one versus zero lane bits; unwritten lanes clear; ±0, ±Infinity, positive and negative NaN payloads, finite signs and subnormals. The real `0EA0E801` word is included. |
| Mask consumers | FCMLT followed by FNEG and BIT or BSL preserves per-lane selection, negative zero, NaN payload/sign and architectural write-zero behavior. |
| FCVTZS / FCVTZU | All scalar F32/F64 to signed/unsigned 32/64 combinations plus SIMD/scalar-vector variants; NaN maps to zero; finite overflow and infinities saturate; exact neighboring threshold values; W writes clear high register bits. |
| CSEL continuation | Original positive-Infinity correction remains visible for EQ and reversed NE; a different compare value or non-minimum sentinel cannot be swallowed. |
| HIR type | `UInt64.MaxValue` carried by the IR `-1` bit pattern is coerced to the unsigned HIR type without losing payload; signed Int64 min/max remain typed and complete. |

Fixtures call the real decoder and private instruction-lifting entry point through reflection. They seed genuine SSA input loads and interpret only the resulting observed IR values. Memoization models one execution of each SSA input, and read-count checks detect repeated evaluation.

The floating-to-integer oracle uses `BigInteger` truncation and integer clamping. The IR interpreter deliberately throws if an unguarded NaN, infinity or out-of-range value reaches `FToSInt` / `FToUInt`; it never lets the host CLR's unspecified overflow conversion accidentally satisfy the tests. Select evaluation is lazy. Floating masks and negation compare raw bits, not merely numerical equality.

The fixed unsigned UInt64-to-F32 combination is deliberately outside the supported lift scope. Its existing HIR `RUn`-then-`R4` path has not proved direct rounding. `n = 2^63 + 2^39 + 1` distinguishes direct F32 rounding (`2^63 + 2^40`) from an actual intermediate double (`2^63`). The new fixture requires explicit unsupported reporting and an untouched destination for that combination. Ordinary nonfixed lowering is unchanged; its IR checks do not certify the existing emitted HIR/IL rounding path.

## Optional original native evidence

The same executable can load the original ELF, metadata and helper signature library directly, then recover a small explicit method selection to HIR. This mode is separate from the deterministic fixtures. Reuse an already archived matching baseline; it is not a reason to repeat baseline capture or the historical test suites. The integration owner chooses one matching native comparison for the candidate.

```sh
dotnet Rewind.Analysis.Arm64Numeric.Tests.dll --native /absolute/libil2cpp.so /absolute/global-metadata.dat /absolute/unity-6000.3.12f1-android-arm64.sig 'AssetKits.ParticleImage.Noise::ValCoord|AssetKits.ParticleImage.Noise::SingleCellular|AssetKits.ParticleImage.Noise::FastFloor|AssetKits.ParticleImage.ParticleData::Simulate' 4
```

This prints input and loaded-analysis hashes, selected method addresses, HIR, notes and remaining recovery problems. The explicit namespace avoids the separate Jobs ParticleData type. A zero-match filter or recovery crash fails the command; other existing HIR problems remain visible evidence rather than being silently labeled successful recovery. No method-name special case is used in the numerical tests or production lifting rules.

This is targeted regression coverage for decoder, IR semantics and constant coercion. It does not claim game rendering, Unity runtime behavior, every ARM instruction, floating exception flags, or all FPCR rounding modes have been validated.
