# Outlined cleanup incremental fixtures

This executable references the newly built Rewind binaries through `RewindBinaryDir`. It does not build
Rewind, load the game model, run native recovery, or run Unity. Root is the sole integration/build/run owner.

Build the fixture project after the single production candidate build, using the same `RewindBinaryDir`
property as the other R25 fixture projects. Run its DLL with:

```
--group shape,identity,frame,eh,order --report <new-report.json> --journal <new-groups.jsonl>
```

`--group` selects only new or invalidated groups. The append-only journal skips prior successful selected
groups for the same analysis, core, and fixture binary SHA-256 hashes. A changed fixture or production
binary does not silently inherit a previous pass; the integration owner still selects only affected groups.

| Group | New contract checked |
| --- | --- |
| shape | Complete bounded A64 body, widths/offsets/branch ordering, immutable GOT, helper EH rejection |
| identity | Exact native MethodDef registration, Address-zero MethodRef context, safe generic sharing, closed arguments, no-return Rethrow |
| frame | Direct sret and complete copied sret, paired lifetime initialization, unknown writes/calls, bit-repacked pointers, disjoint receiver/frame, live result rejection |
| eh | Exact full BL coverage, pad-zero propagation, matching recovered catch scope, rejected catch-all/cleanup/gap, missing raw exception-edge diagnostic |
| order | Real expanded IR, receiver/descriptor identity, Dispose before pending load, null continuation, exact rethrow identity, alias changes, Dispose throwing |
| boolean-projection-delta | Live Boolean return used by a loop branch; exact return slot/width and disjoint call proof; rejected pointer/byref/native-int/unknown returns and overlapping receiver extent |

For the follow-up to the first R25 after probe, select **only** the new group:

```
--group boolean-projection-delta --report <new-delta-report.json> --journal <new-delta-groups.jsonl>
```

The original five cleanup groups and three receiver groups already passed their first run (136 assertions
combined). This delta does not rerun them. Its production change only accepts an ordinary A64 x0 projection
when the source call independently passes the existing frame-disjointness proof and its bound ABI is
specifically Boolean. Other scalar return types and address-shaped returns remain outside this exception.

The fixture supplies explicit in-memory ELF/model tables to the actual recognizer and pass. It is not an
ELF parsing or relocation-loader test. Those input facts come from the frozen R24 real-image evidence.
The small IR interpreter checks only the accepted expansion's order and branching contract, not game
runtime equivalence. A zero diagnostics count would not be runtime acceptance.

The production change intentionally keeps an unproved caller as an opaque native call. In this batch the
real AddToTaskList normal cleanup has the direct-sret proof. BinaryDeserialization's complete copied-sret
initialization is supported, but its unresolved indirect calls still block the lifetime-effects proof.
