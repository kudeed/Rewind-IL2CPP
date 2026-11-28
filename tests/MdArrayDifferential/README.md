# ARM64 rank-two reference array recovery checks

These checks exercise the original mj0 binary (SHA-256
f0808ccac104a950c6b99a3f4a148c21ae0daed078105714b14ac2b58f1dd583) and the
actual Assembly-CSharp emitted by Rewind. They do not use a handwritten replacement
for the recovered method.

## Scope

- Native RefreshTextPowerInAllFloor (060018F5, 184 bytes): execute the entire method,
  including its original GetLength calls, array reloads, loop branches, bounds failures
  and item callback sequence. Copy the entire actual emitted method into a CLR fixture.
- Native rank-two reference getter (020738A0, 56 bytes): execute the complete getter.
  Compare against the actual emitted GetValue/cast expressions from 060018F5 and
  the first out-of-line getter replacement in 060018FA. Only the three live inputs
  (array, row and column) are rebound; original conversions, arithmetic and calls remain.
- Native camera corner path (06001BB0): enter the state-1 arm at 0259A594, stop
  after its fourth CalculateCamIntroducePos call, and retain original exception
  paths. Copy exactly the corresponding emitted IL prefix, its original throw blocks,
  and seed its incoming controller local. Subsequent camera animation is outside this fixture.

The fixtures map original managed call boundaries to instrumented Array.GetLength,
item refresh and position callbacks. Calls introduced to project native bounds are
ordinary CLR calls, not injected external boundaries. Replacement actions run only at
original boundaries, so the tests can distinguish saved array identities from fresh
field reads. Callback exception type, call order, final array identity and state field
are compared. The position callback result is an opaque three-float fixture value.

There are 150 native cases and 240 CLR comparisons: 90 getter cases checked against
both actual expressions, 28 full scan cases, and 32 camera-prefix cases. Cases cover
null arrays/items, empty dimensions, negative and out-of-range indices, nonzero and
extreme legal CLR lower bounds, callback exceptions, and replacements at the original
call boundaries. A fourth-corner case explicitly uses a saved D array and a column
length from a fresh E array; neither is substituted for the other. Unsigned live inputs
from packed 32-bit positions are bound by zero-extending their original 32-bit bits.

The source imports fixture definitions from their actual Cecil metadata to preserve
complete multidimensional return/field signatures, rather than editing recovered IL.

## Running

Build the CLI first, then pass its compiled directory as RewindProbeArtifacts.

    dotnet build tests/MdArrayDifferential/MdArrayDifferential.csproj -c Release \
      -p:RewindProbeArtifacts=/absolute/path/to/Rewind.Cli/release -warnaserror
    python3 tests/MdArrayDifferential/native_oracle.py \
      /absolute/path/to/oracle-output /absolute/path/to/libil2cpp.so \
      /absolute/path/to/recovery-workflow
    dotnet tests/MdArrayDifferential/bin/Release/net10.0/MdArrayDifferential.dll \
      /absolute/path/to/Assembly-CSharp.dll /absolute/path/to/new-result-directory \
      /absolute/path/to/oracle-output

The workflow directory supplies the existing method_evidence.Elf, Unicorn and
Capstone environment; no package installation is required. The native script verifies
the entire original input hash and records individual body hashes. The CLR runner
records source DLL, fixture, native oracle and binding manifest hashes, writes the
full per-case comparison, and returns nonzero on any mismatch.

Run ILVerify on MdRecovered.dll with the matching runner DLL and host BCL references
to validate all four adapted methods. The root full export remains the gate for the
unadapted complete game assembly.

Additional tests:

- tests/Arm64MultiArrayShapeSmoke: three positive complete-function shapes and
  507 negative shapes, including every single-bit mutation, truncations, wrong throw
  helper and overflowing function address.
- tests/MdArrayRuntimeSmoke: three actual native methods and thirteen IR mutations
  after normalization. Removal or reversal of bounds guards, array identity mismatch,
  non-eight-byte reference stride, unchecked high bits, delayed null failure and
  overflowing induction must retain diagnostics. Takes native, metadata, signature,
  and fresh output directory arguments; serialize large model runs with the shared lock.

This change is restricted to readonly rank-two arrays with known reference elements.
Creation, stores, open generic/value-type element access remain diagnosed. In
particular InitMaze is not a completed method in this batch.

## Producer evaluation regression

MdArrayRuntimeSmoke also uses the actual MdElementRead and BodyEmitter to emit
call-producer and field-producer fixtures. MdArrayEffects compares their execution
with explicit argument-production events followed by the complete original native
getter. All 28 cases require one array evaluation, row then column production before
the first dereference, and preserved exceptions. Removing receiver capture from the
actual emitted IL is a deliberate negative control: 15 call cases and 2 field cases
detect it. These synthetic producer cases supplement, rather than replace, the 240
original-game-method comparisons.

    python3 tests/MdArrayEffects/native_effects_oracle.py /absolute/path/to/effect-oracle
    dotnet build tests/MdArrayEffects/MdArrayEffects.csproj -c Release \
      -p:RewindProbeArtifacts=/absolute/path/to/Rewind.Cli/release -warnaserror
    dotnet tests/MdArrayEffects/bin/Release/net10.0/MdArrayEffects.dll \
      /absolute/path/to/effects-emitter-output /absolute/path/to/effect-oracle \
      /absolute/path/to/fresh-effect-results
