# SCP10 packet recovery and current delivery status

Checked on 2026-10-29 against main
`c7d2992c89c16d85237e18557ff292979b3a67b4` for tracker
[#8271](https://github.com/LionSR/TNLean/issues/8271) and the quantum-double
source-construction owner [#8947](https://github.com/LionSR/TNLean/issues/8947).
This is a bounded source/provenance audit, without Lean elaboration or a build.

## Published work and its scope

- [#8707](https://github.com/LionSR/TNLean/pull/8707) merged on 2026-10-08 as
  `73e1ec4cecbd5b6a907b3f98ce16e7c3d097362e`. Its packet contains flux
  deformation and local quantum-double projector identities. Its PR explicitly
  leaves full-lattice kernels and physical T-to-K transport separate.
- [#8726](https://github.com/LionSR/TNLean/pull/8726) merged on 2026-10-08 as
  `a6238a4b60f9dee3af57ef4d7d369c7b13d0e0e3`: finite rectangular path deformation.
- [#8729](https://github.com/LionSR/TNLean/pull/8729) merged on 2026-10-08 as
  `ff0dac2d10fc74cd9d75d798d8fb3d74b8e8bd1b`: collared open-boundary deformation.
- [#10364](https://github.com/LionSR/TNLean/pull/10364) merged on 2026-10-30 as
  `7649f04fd106f8c85f0bad35557331d1ed9e9840`. It proves the
  actual four-site elementary-to-K contraction for every finite group, including
  physical permutation, boundary map and normalization. This is one block;
  full-lattice placement, common kernels and topology remain outside that PR.

## What was recovered

The exact packet identifiers `7f90643b` (full lattice kernel) and `b2b9fff3e`
(additional six-spin readout), cited by the old tracker, do not resolve as Git
objects in this checkout. GitHub's commit endpoint also reports no commit found
for either identifier. Targeted issue searches return only #8271. This does not
establish that no copy exists elsewhere; it means those identifiers currently
provide no inspectable proof artifact here.

A separate, genuine partial recovery exists:

- Archive branch `codex/scp10-recovery-archive`, commit
  `ca5273cd335633e0aea2e4930c897d732b8260de`, under
  `docs/recovery/scp10-20261005/`.
- Restoration branch `codex/scp10-quantum-double-restore`, commit
  `a40184a42521cc1a11a0e99ee1ee4813b554f073`, published in
  [#8775](https://github.com/LionSR/TNLean/pull/8775), which is closed and unmerged.
- The restoration's own
  [audit](https://github.com/LionSR/TNLean/blob/a40184a42521cc1a11a0e99ee1ee4813b554f073/docs/audits/2026-10-06_scp10_restoration.md)
  explicitly records incomplete source closure and no current compilation.

All 20 archive manifest hashes were checked against the actual archived bytes.
Of the 19 restoration entries in scope, 17 Lean files remain byte-identical at
the final restoration head; the Blueprint leaf and historical audit differ.
These 17 files include two obsolete test fixtures, so this is not a proposed
17-module production delivery. No archive file was copied into the current tree.

The manifest labels six of those 19 entries as historical original-hash matches
and thirteen as reconstructions. Its separate historical digest table
corroborates four of the six original-hash labels. In particular, the lattice
gauge and Hamiltonian files are marked reconstructed. The old reviewed-packet
identifiers cannot be attached to those reconstructed files as acceptance.

The archive's historical original-spin commit
`04105be3202480fbb0c0e81d7f59defeb47de2e3`, integration commit
`791f42a4c8449c84640030369f21a6f0b9596500`, and integration tree
`550dc9698b49813810fb07930a14cecd7c32ec70` are also absent locally. The two
historical commits do not resolve through GitHub's commit endpoint.

## Mathematical frontier in the actual source

The restoration contains `QuantumDoubleLatticeGauge.lean` and
`QuantumDoubleLatticeHamiltonian.lean`. The latter states positivity,
pairwise commutation of the placed terms, and equivalence of the total kernel
with the common kernel. That equivalence is not a spanning theorem.

Its `QuantumDoubleLatticeBlocking.lean:6` imports the absent module
`TNLean.PEPS.Examples.QuantumDoubleLatticeSourceParent`. Neither that module nor
`QuantumDoubleLatticeNativeParent` exists in main, the archive, or the final
restoration tree. The archive's digest table names the latter but contains no
corresponding source bytes.

The original-spin ground-space file has no supplied kernel-classification
hypothesis. Instead, its dimension and spanning wrappers call the missing
`finrank_ker_quantumDoubleKLatticeHamiltonian` and
`ker_quantumDoubleKLatticeHamiltonian_eq_commutingClosureSpan`. They therefore
do not constitute a completed proof of that classification. The restoration
audit identifies the missing mathematical steps: flat-supported,
gauge-invariant coefficient reconstruction; flat-configuration orbit sums as
actual twisted K states; native parent comparison; and the commuting-pair
conjugacy-class dimension. Existing generic PEPS classification must be checked
for reuse before implementing these steps.

The final restoration pin is Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, and QICLean
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`. Its source retains periods at least
three, the nonabelian clockwise multiplication order, and normalized bond
averages. Its preliminary source comparison is not an independent completed
faithfulness review. Reuse requires current dependency/API validation, complete
source closure, source-statement review and hosted acceptance. It must also
follow the current no-fixture policy.

The unlocated extra readout packet does not erase the already merged charge
pair and endpoint-readout results. It supplies no additional verified coverage.
No duplicate full-kernel implementation, reopened restoration PR, new proof
claim, or repository merge follows from this audit.
