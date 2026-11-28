# Adjacent primitive array reads

This runner exercises only the new HIR wide-array-read boundary against an existing build of Rewind.Analysis/Core. It does not run the historical numeric, InlineTemplates or ValueSnapshots suites.

The fixture uses the actual address decomposition, `LoadSem`, `DecideMaterialization`, `Materialize`, truncation and bits-to-float semantics. A separate ordinary-array interpreter checks typed values, read order, null/bounds failures and survival across later aliasing writes. Float cases include signed zero, distinct NaN payloads and both infinities. Primitive byte/halfword/word ranges exercise the same width proof.

Accepted shapes are complete primitive elements at aligned, typed SZ-array addresses and scalar native widths no greater than eight bytes, with a planned complete snapshot and address operands that contain no unproved calls. Repeated field paths must be readonly/literal at every level; mutable array/index fields are refused because a native address was only evaluated once. Partial/misaligned elements, mismatched scales, Boolean bit packing, effectful address computations, unproved 64-bit index coercions and a single-use read without a planned snapshot remain explicit recovery gaps. No exception fallback or indexing mask is added.

The snapshot fixtures model managed null/index exceptions. They do not claim to define the behavior of an original unchecked native access outside allocated array memory, concurrent mutation by another thread, volatile accesses, or native memory faults.

Build this project once against the new isolated CLI directory with `-p:RewindBinaryDir=/absolute/path/to/src/Rewind.Cli/bin/Release/net10.0`, then run its DLL. The JSON report records only this runner's new groups/assertions.
