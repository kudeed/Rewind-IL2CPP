# Rejected C# member evidence: incremental fixtures

This suite invokes the production read-only evidence writer by reflection. It does not recover native methods,
rewrite IL, run Unity, or run historical Rewind suites. The exact DLL bytes are the oracle: sidecar method-body
bytes are compared with a separate `PEReader`, and the input DLL hash must be unchanged after success and failure.

New groups:

- `eh`: catch/finally/filter clauses, original region offsets and original function-pointer instructions survive.
- `branches`: a valid short branch at displacement 127 and an original switch table remain byte-for-byte intact.
- `locals`: native-int locals, live pointer reads, and `ldloca` / `ldloca.s` remain original evidence.
- `metadata`: complete body/IL bytes, literal unresolved operands, strict rejected-token selection, duplicate
  rejection deduplication, and an evidence-output failure that cannot alter the DLL.
- `native`: one source-only invocation on the already captured BehaviorDesigner v3 DLL. Requires
  `--source-assembly`; writes C# and IL sidecar using the existing input dependency directory. It must retain
  the ILSpy rejection and all opaque recovery markers. This is not a native export or runtime equivalence test.

The default selects the four synthetic groups. Native integration is explicit, for example:

```sh
dotnet run --project tests/Rewind.Output.RejectedMethodEvidence.Tests --no-build -c Release -- \
  --group native \
  --source-assembly /var/tmp/pap-r24-behavior-v3/assemblies/BehaviorDesigner.Runtime.dll \
  --work-dir /var/tmp/pap-r24-rejected-evidence-native \
  --journal /var/tmp/pap-r24-rejected-evidence-native/groups.jsonl \
  --report /var/tmp/pap-r24-rejected-evidence-native/results.json
```

Every group appends its result immediately to the journal. If a group fails, fix that concrete issue and pass
only its group name on retry; do not rerun passed groups. The report records the exact `Rewind.Output.dll` hash.
No fixture has been run merely by adding this project.
