# R25 receiver recovery fixtures

This project references a previously built production binary directory through `RewindBinaryDir`. It has no project references and does not rebuild Rewind. It exercises only the new receiver proof, selection and emitted-call semantics. It does not run Inline/Numeric/REV64/SinCos, R24 dispatch suites, a game export, or Unity.

Build the fixture project once against the integration binaries, then run each selected group with a persistent JSONL journal:

```sh
dotnet build tests/Rewind.ReceiverRecoveryFixtures/Rewind.ReceiverRecoveryFixtures.csproj -c Release -p:RewindBinaryDir=/absolute/integration/bin
dotnet tests/Rewind.ReceiverRecoveryFixtures/bin/Release/net10.0/Rewind.ReceiverRecoveryFixtures.dll --group raw-proof --journal /absolute/evidence/receiver-groups.jsonl --report /absolute/evidence/receiver-raw-proof.json
dotnet tests/Rewind.ReceiverRecoveryFixtures/bin/Release/net10.0/Rewind.ReceiverRecoveryFixtures.dll --group receiver-selection --journal /absolute/evidence/receiver-groups.jsonl --report /absolute/evidence/receiver-selection.json
dotnet tests/Rewind.ReceiverRecoveryFixtures/bin/Release/net10.0/Rewind.ReceiverRecoveryFixtures.dll --group call-semantics --journal /absolute/evidence/receiver-groups.jsonl --report /absolute/evidence/receiver-call-semantics.json
```

A group already marked `pass` for the exact fixture/Analysis/Core/Output binary hashes is reported as `skip-pass`. After a failure, rerun only the failed group. If a binary changes, select only the groups affected by that change; the journal keeps each binary identity separate.

## Groups

| Group | New coverage |
| --- | --- |
| `raw-proof` | Synthetic AArch64 through the actual raw lifter; complete function bounds; overwritten x0; actual reads, branches, tail forwarding, unknown instruction; ABI-dead void return inputs and pure phi paths; EH landing-pad refusal; exact singleton/nonforwarded/nongeneric/noninterface target. |
| `receiver-selection` | Actual linked model, ProgramAnalysis, ABI and HirBuilder constructors; the production BuildCall entry; stale bool/object[]/Decimal-like values; safe same-class this; checked receiver priority; static/different-class failure; pending call evaluation; materialized HLocal held-phi bookkeeping; deferred nullable-field refusal; exact proof identity retained by HirCopy and HIR printing. |
| `call-semantics` | Actual AssemblyEmitter/BodyEmitter IL and an in-memory emitted assembly: recovered `call` accepts null this, existing `callvirt` throws, old receiver effect runs once before the recovered call, retargeted/virtualized proof is rejected. |

The `MetadataFile` and `Il2CppBinary` private constructors are invoked by reflection to build a small valid empty model. The model, ProgramAnalysis and HirBuilder use their actual constructors. Reflection reaches the narrowly tested internal proof/selection/materialization functions; it does not fabricate an uninitialized builder or seed proof-cache success.

The tests establish these local invariants. They are not a proof of full PopTask, Unity, or native/managed program equivalence. Native acceptance and refusal for the selected real methods must be reported separately by the integration runner.

Revision 2 corrects the checked-receiver model to use a declared, initialized same-class local and assert preservation of that exact expression. Production sources are byte-identical to revision 1.

Revision 3 adds a bounded recursive closed-signature check to the receiver proof and three new raw-proof negatives: a bare generic return, a bare generic hidden in nested arrays, and a generic instance with the wrong arity. This revision also remains unbuilt and untested by its author.

Revision 4 checks reachable native return/control encodings before the ABI-dead return exception: ordinary RET through x30, no computed LR or x30 base writeback, no hidden pointer-authentication controls/hints. The existing raw-proof group gains RET-x0, MOV-to-LR, writeback and hint negatives plus ordinary NOP/BTI positives. No tests were executed during preparation.
