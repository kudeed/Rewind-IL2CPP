# Experimental Rewind checkpoint: mj0 to Bus Fever Party

This branch saves ongoing recovery work before the user-ended StickHero project
is cleaned up. It is not a complete recovery, release, or Android acceptance.

## Included source

The parent a4429cbac68d7e1cc1afcb8ba20aa921ea7bdc35 is the last full
same-input nonregression checkpoint (188 remaining ILVerify diagnostics).
This tree also contains the following completed source batches:

- Exact fresh object-array stores.
- Signed scalar projections and projected enum stack boxes.
- Complete List values, shared resize, and single-evaluation captures.
- ARM64 HFA return lanes.
- Rank-2 reference-array reads with single evaluation.
- Fresh carried List.Clear counts with all-path and effect checks.
- Preservation of original native type guards and NullReferenceException paths.

The prior full-07 export reduced ILVerify diagnostics from 188 to 175 but was
REJECTED by the body marker gate: CardExpanding2D.Update and PlayerFloor.SpawnRewards
exposed unresolved static-getter outputs after HFA lanes were restored. Those
unresolved paths have not been converted to no-ops or accepted as complete.

The last two batches have isolated proofs. List.Clear was checked across 8165
bodies (3 changed / 8162 identical); its isolated ILVerify count was 179 to 172,
with no added diagnostics and identical 476 references. That baseline is not
full-07. Native type-guard preservation has 12-method HIR A/B evidence, 3 changed
and 9 identical; it has not received a final combined ILVerify export.

## Excluded candidates

Static getter copies are conditional WIP: equivalence requires generated flag
values in {0,1}, but exclusive writes to those bytes are not proven. The original
candidate proof is superseded by the independent review and WIP status archived
with the workflow. The int32 rank-2 extension is unvalidated WIP. Neither is in
this source tree.

## Validation and next scope

One warnings-as-errors CLI compilation validates this combined source checkpoint.
Previously passed unchanged branch tests are reused with their source hashes;
the discontinued game's full export and runtime tests are not repeated.
No CI, Player, APK build, or release is part of this checkpoint.

The next input is Bus Fever Party 1.3.6. Freeze its input hashes, produce one
baseline, group actual recovery failures by common cause, repair those causes
in batches, and then wire the game in batches. Only affected branches and their
integration boundaries are retested. This source remains experimental until
the new-input stage gates pass.
