# ARM64 REV64 incremental regression

This independent executable covers the new `VecKind.Rev64` decoder/lifter change.
It does not run or modify `Arm64Numeric.Tests` or any historical suite, and does
not launch Unity or native recovery. The integration owner builds and runs it
once against the newly built CLI/Lab dependency directory.

## Scope

The accepted vector encoding has `(word & 0xBF3FFC00) == 0x0E200800`, with
`size != 3`. Q and size select `8B`, `16B`, `4H`, `8H`, `2S`, or `4S`.
There is no scalar form and no 64-bit-element arrangement. The adjacent U=1
REV32 and opcode-neighbor REV16 encodings must not be accepted as REV64.

Within each 64-bit block the instruction reverses the order of whole elements.
It does not reverse the bytes inside an element or reinterpret floating-point
values. A 64-bit vector write clears the upper 64 bits. The lifter gathers the
input nodes before writing the destination, so `Rd == Rn` is supported.
`VecKind.Rev64` is appended as ordinal 77, preserving the previous
`FCmLtZero` ordinal 76 and all earlier enum values.

The fixtures cover:

- Six explicit instruction words and six literal expected byte sequences.
- Nonconstant SSA input nodes, distinct and aliased registers, and V31 as an
  ordinary SIMD register.
- Signed zero, infinities, quiet/signaling NaN payloads, subnormals, and arbitrary
  integer bits. The small IR evaluator rejects floating-point operations.
- Upper-half clearing, involution when executed twice, and untouched distinct
  source registers.
- Source input loads evaluated once through SSA memoization.
- Reserved element sizes/scalar encodings, neighboring REV32/REV16 encodings,
  and fixed-field mutations that must not alias to REV64.
- Defensive lifter rejection of malformed scalar or 64-bit-element Rev64
  instructions even if they are supplied without the decoder.

## Original native anchors

These five instructions are from `AssetKits.ParticleImage.ParticleData.Simulate`
in the existing `r19-particle-image/NATIVE.json.gz` and annotated native evidence.
All five are `REV64 Vd.2S, Vn.2S`.

| RVA | Word | Destination | Source |
| --- | --- | --- | --- |
| `0x6E4B620` | `0x0EA00863` | V3 | V3 |
| `0x6E4B624` | `0x0EA00800` | V0 | V0 |
| `0x6E4B734` | `0x0EA00860` | V0 | V3 |
| `0x6E4B850` | `0x0EA00802` | V2 | V0 |
| `0x6E4B9F8` | `0x0EA00900` | V0 | V8 |

The native before/after recovery is owned by the integration runner, which
reuses its archived d3fcff baseline. It is not duplicated here.

## Run after the integration build

Pass an absolute directory containing the freshly built `Rewind.Analysis.dll`
and `Rewind.Core.dll`. Do not point to a stale baseline directory.

```sh
dotnet build tests/Rewind.Analysis.Arm64Rev64.Tests/Rewind.Analysis.Arm64Rev64.Tests.csproj \
  -c Release -p:RewindBinaryDir=/absolute/new-cli-bin -m:1
dotnet tests/Rewind.Analysis.Arm64Rev64.Tests/bin/Release/net10.0/Rewind.Analysis.Arm64Rev64.Tests.dll \
  --report /absolute/evidence/rev64-tests.json
```

The JSON report records the actual loaded Analysis binary SHA256, assertion
count, and passed/failed groups. A failing group returns a nonzero exit code.

Only the two SIMD source files and these three new test files are changed by
this subtask. No fixture has been built or executed by its author; actual
results must come from the integration owner's single new-test run.
