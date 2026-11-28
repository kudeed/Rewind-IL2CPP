# Fully shared generic runtime regression

Build the CLI first. Set `RewindProbeArtifacts` to its directory containing Rewind.Analysis.dll and Rewind.Core.dll when building this console test. Run the resulting test DLL with four arguments: original native ELF, original metadata, Unity signature file, output directory. The test rejects input hashes other than the frozen mj0 input pair.

The test runs the real lifting and managed-recovery pipeline on four positive methods, then makes 34 isolated IR mutations. Each broken invoker target, argument table, runtime size, marshalling predicate, or stack-canary proof (including loop backedges, original array bounds guards, and frame escape before initialization) must retain a recovery diagnostic. Canary failures specifically must retain StackCheckFail. JSON and HIR evidence is written to the requested directory. Native model loading must use the server's shared model.lock when other probes or exports are active.

The companion FullySharedAbiSmoke test verifies supported signature selection and rejects other ABIs without loading the native model.
