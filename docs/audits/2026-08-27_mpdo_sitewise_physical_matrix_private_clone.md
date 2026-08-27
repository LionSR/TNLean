# MPDO physical-transport private clones

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for two private duplications in the
physical-transport modules of the MPDO layer. Every name listed here was
`private`, so no deprecation alias is warranted and no blueprint `\lean{}`
tag cited any of them.

## Sitewise physical matrix re-declaration

`TNLean/MPS/MPDO/PhysicalSectorProductTransport.lean` privately re-declared
the sitewise tensor power of a one-site matrix, already available as
`MPOTensor.sitewisePhysicalMatrix` in
`TNLean/MPS/MPDO/SitewisePhysicalMatrix.lean`, and reproved its isometry,
coisometry, and MPO-transport lemmas from scratch.

| Removed | Replacement |
|---|---|
| the body of `MPOTensor.PhysicalSectorFactorization.physicalCoordinateMatrixN` (private) | the name survives as a reducible `abbrev` for `MPOTensor.sitewisePhysicalMatrix F.physicalCoordinateMatrix N` |
| the proof of `…physicalCoordinateMatrixN_isometry` (private) | `MPOTensor.sitewisePhysicalMatrix_isometry` |
| the proof of `…physicalCoordinateMatrixN_coisometry` (private) | `MPOTensor.sitewisePhysicalMatrix_mul_conjTranspose` with `MPOTensor.sitewisePhysicalMatrix_one` |
| the proof of `…physicalCoordinateMatrixN_mpo` (private) | `MPOTensor.singleKrausMap_sitewisePhysicalMatrix_mpo` |
| `…reindex_physicalCoordinateMatrixN_windowComplement` (private) | `MPOTensor.reindex_sitewisePhysicalMatrix_windowComplement` applied to `F.physicalCoordinateMatrix`, at both of its former call sites |
| `MPOTensor.reindex_sitewisePhysicalMatrix_windowComplement` (private copy in `TNLean/MPS/MPDO/PhysicalSupportProductTransport.lean`) | the same statement, now public in `PhysicalSectorProductTransport.lean`, which the support module transitively imports |

The window-complement lemma was byte-identical in the support module and, in
the sector module, a specialization of it. The general statement is hosted in
`namespace MPOTensor` of `PhysicalSectorProductTransport.lean`, the shallowest
file that already imports both `SitewisePhysicalMatrix.lean` and
`ParentHamiltonian/CyclicWindowIndex.lean`. The two former call sites in the
support module resolve the bare name unchanged.

`physicalCoordinateMatrixN` is deliberately kept as a `noncomputable abbrev`
rather than a `def`: its reducibility is what lets `rw` at the two retargeted
call sites key on `sitewisePhysicalMatrix`. The one entrywise proof that
relied on unfolding the old body,
`…physicalCoordinateMatrixN_two`, now names `sitewisePhysicalMatrix` in its
`simp` set.

## Blocked-coordinate channel transport

`TNLean/MPS/MPDO/PhysicalSectorPhysicalTransport.lean` spelled out the same
reindex/conjugate/reindex composition four times, together with four copies of
its trace-preserving complete positivity proof.

| Removed | Replacement |
|---|---|
| the four hand-written bodies and type ascriptions of `…physicalBlockOneMap`, `…physicalBlockOneInverseMap`, `…physicalBlockTwoMap`, `…physicalBlockTwoInverseMap` (all private) | the names survive, each defined by the new private `blockTransportMap` at two coordinate equivalences and one isometry |
| the four proofs of `…physicalBlockOneMap_isKrausCPTP`, `…physicalBlockOneInverseMap_isKrausCPTP`, `…physicalBlockTwoMap_isKrausCPTP`, `…physicalBlockTwoInverseMap_isKrausCPTP` (all private) | the names survive, each a single application of the new private `blockTransportMap_isKrausCPTP` |

All eight names are retained because the four closure lemmas and the public
capstone `NeighboringTraceFactorization.blockTwo_isRFPViaTS` consume them by
name; only their bodies collapsed. The four closure proofs and the capstone are
untouched.

`blockTransportMap_isKrausCPTP` opens with `classical` rather than binding a
decidability instance on the isometry's target index: the statement does not
mention that instance, and binding it draws the unused-instance linter.

The pattern is recorded as a promoted entry, *blocked-coordinate transport of a
channel*, in `docs/tactic_patterns.md`.

## What was checked

A root `lake build` is clean. `scripts/check_forbidden_lean_tokens.py`,
`scripts/check_numbered_lean_files.py`,
`scripts/check_oversized_lean_files.py`, and
`scripts/generate_import_aggregators.py --check` all pass. No file lost all of
its declarations, so no aggregator changed. No blueprint source mentions any
removed name.
