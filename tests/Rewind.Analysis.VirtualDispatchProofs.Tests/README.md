# Virtual dispatch proof fixtures

These are five new groups for the R24 review correction. They exercise the real private `HirBuilder` resolution helpers through reflection, with a normally constructed `HirBuilder`, real CFG dominators, AAPCS64 ABI, signature interning, an empty normalization result and explicit metadata/vtable identities. No native input is loaded and no historical test suite is invoked.

The model is assembled in memory because the public `Il2CppModel` constructor parses linked metadata tables. Its image, binary version, signatures, method/type tables and address indexes are initialized explicitly. `ProgramAnalysis` supplies the model, layout calculator, ABI, helpers and context needed by these bounded helper probes. This is not a whole-pipeline or runtime-equivalence test.

| Group | New risk covered |
| --- | --- |
| `declared` | Ordinary/inherited contracts remain valid; a unique descendant, open generic descendant or unrelated sibling cannot prove an unguarded base receiver has a new slot. |
| `dominance` | Only the successful type-test side has the fact; join, unreachable and different SSA-object cases reject it. Interface-relative slot zero must not replace class-vtable slot zero; weaker facts retain a more precise inferred class. |
| `pointers` | A fact established after earlier function-pointer reads cannot be used in either merged-pointer helper or `VirtualPointer`; facts that dominate each original read remain usable. Receiver identity and unknown read locations stay conservative. |
| `precision` | Fully substituted generic ancestors preserve exact types; different generic arguments and inferred interfaces do not override a proven class. Missing CFG, unknown/unreachable locations and mismatched current positions remain conservative. |
| `casts` | A unique cast on another branch or later than a side-effecting call cannot refine the current receiver. Current dominating casts are retained, without moving them to an earlier pointer read. |

The fixture explicitly seeds semantic meanings and successful type-test facts to isolate resolution policy. It does not duplicate the production resolution algorithm. Negative cases deliberately contain incomplete receiver evidence and expect refusal, rather than a guessed method.

Build once against the candidate CLI output, then run only these groups:

```sh
dotnet build tests/Rewind.Analysis.VirtualDispatchProofs.Tests/Rewind.Analysis.VirtualDispatchProofs.Tests.csproj -c Release -p:RewindBinaryDir=/absolute/candidate/bin
dotnet tests/Rewind.Analysis.VirtualDispatchProofs.Tests/bin/Release/net10.0/Rewind.Analysis.VirtualDispatchProofs.Tests.dll --report /absolute/report.json --journal /absolute/groups.jsonl
```

`--group declared,dominance,pointers,casts,precision` selects groups. Each group appends a JSONL result immediately, including a run id and assertion count. If one group fails, preserve the journal and rerun only the failed group after fixing its concrete cause. All old Inline, Numeric, REV64, wide-array and SinCos suites are outside this test command.

The previous full BehaviorDesigner/Astar exports are historical evidence. Their absence of diagnostics does not establish runtime equivalence. A stricter proof policy may correctly restore diagnostics that the descendant fallback previously hid.
