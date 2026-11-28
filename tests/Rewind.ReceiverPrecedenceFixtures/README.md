# R25 dominating receiver follow-up

This independent project contains only the new `dominating-receiver` group. It references already built production binaries through `RewindBinaryDir`; it has no production project references and does not execute the original 56 receiver assertions.

The regression is the real `BinaryDeserialization.Load` call at `0x43746B4` to `ParentTask.AddChild` at `0x43810D8`. The caller has already checked the same receiver as `ParentTask` on every path reaching the call. The new unused-receiver fallback previously examined only the expression's base `Task` type and throwing cast guards, then replaced the valid receiver with an unresolved null. The callee genuinely reads `this`; it must keep ordinary call semantics and the original receiver identity.

The fixture constructs the metadata/model, ABI, ProgramAnalysis, HirBuilder and CFG through their actual constructors. It seeds the existing type-test fact at its success block and exercises the actual private BuildCall path. A real diamond tests dominance across two incoming call edges; a bypass path and a sibling-class fact must still reject. The target's synthetic A64 body reads memory through entry x0. The positive case uses a static caller, so inventing current `this` cannot accidentally satisfy it. Assertions check the original declared local, both managed arguments, diagnostics and absence of a direct-call attestation.

This delta tests precedence of an already established type fact. It does not rerun R24 type-test discovery or the first R25 raw-proof, receiver-selection and emitted-IL groups, and it does not establish complete BinaryDeserialization/native equivalence.

Root owns build and execution. Build this project with `-p:BuildProjectReferences=false -p:RewindBinaryDir=<compiled-cli-directory>` and run only:

```text
Rewind.ReceiverPrecedenceFixtures.dll --group dominating-receiver --journal <new-jsonl> --report <new-json>
```

The mandatory JSONL journal uses the fixture, Analysis and Core binary SHA-256 values and skips a prior passing result for the same identity.
