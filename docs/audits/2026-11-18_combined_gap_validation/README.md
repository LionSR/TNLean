# Controlled combined gap integration validation

Snapshot: A d76317024, B 0cffa14cb, owner dedup 65f5f59a, gap b61f2bce,
generic scope 8b6023e4, documentation 43a3bf39 and 1218a519.
Local proof repairs: bcedce188 (argument indentation) and 9c4f017c4
(explicit angular witnesses; equivalent author commit 1a44b4fe5 omitted).
No shared PR branch was modified.

This is a partial validation record, not full-library or mathematical clearance.
50 of 89 production targets passed strict checks; gap subset 27 of 52.
Six regression scripts passed; generic_gap_boundary_regression remains unvalidated.
The 658 additional reverse-import consumers have not been validated as a group.
The build was interrupted for disk safety before this record. Files with changed
or missing transitive dependencies were excluded from strict to avoid stale-cache
false passes. See validation-ledger.json for individual reasons.

Subsequently removed only generated *.setup.json under this task's TNLean and
private QIC .lake/build/ir directories, freeing 4,616,900,608 bytes. Lake v4.36.0-rc1
Lake/Build/Actions.lean compileLeanModule rewrites those configurations before
compilation. All oleans, sources, branches, logs and validation records were kept.
This resource recovery does not constitute additional validation.

## Boundary regression follow-up

`scripts/zero_gap_tn_wrappers_regression.lean` passed the repository strict Lean
flags without emitting oleans. It directly invokes Rectangle projector-gap
transport at zero Hamiltonian, q=2, Delta=0 for arbitrary width and height
(including 1x2, zero width and zero height); both canonical and pinned zero-floor
optimizers for empty nested regions with weight one for every m (including 0
and 1); and ThreeWay centered zero-chain transport for every natural j,m.
The optimizer results retain Delta-weighted fidelity, without uniqueness or an
unweighted fidelity conclusion. These are actual wrapper calls, not QIC-only tests.

RangeSquareGroundState and BoxEntropySupremum are NOT covered by that fixture.
Their production dependency validation is delegated to the other worker. No
production builds were run here after that handoff. Selector tests confirm changes
to each of the four covered owner modules select the new regression, including
SquareZeroFloorOptimizer through its transitive import. No CI policy was weakened.
