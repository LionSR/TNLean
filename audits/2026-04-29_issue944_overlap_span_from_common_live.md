# 2026-04-29 — Issue #944 overlap-span from common live-sector comparison

## Scope and issue-thread check

This branch continues the non-Gemma canonical-form equal-case path after merged PRs #987,
#988, and #989. The current issue-thread state is:

- #944 has reduced the collapsed-BNT representative obligation to the finite-length span
  equality for the two live block families.
- #970 has the common phase-cover span mechanism and the BNT proportional-decomposition
  comparison route on `main`.
- #942/#969/#989 provide common physical blocking length and relabeled cyclic-sector families
  with zero-tail bookkeeping, while leaving the physical-label compatibility,
  injectivity/Wielandt refinement, and final BNT comparison data explicit.
- #652 remains the umbrella for closing the non-periodic CPSV/CPGSV equal-case
  canonical-form theorem from `SameMPV₂`.

The new theorems therefore do not assert that arbitrary `SameMPV₂ A B` already gives the
final span equality. Instead they compose the available common-cover and BNT comparison
machinery with the exact-live and zero-tail sector comparison theorems, making the
remaining inputs precise.

## Paper/source anchors

The statements follow the standard MPS route used in the canonical-form proofs:

- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 271--280 define the basis of
  normal tensors and its minimality condition; line 279 states that each normal tensor in
  the canonical form is related to a basis tensor by a nonsingular matrix and a phase.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 283--302 write the MPV expansion
  over BNT blocks, with the coefficient sum over sector weights on lines 300--301.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 349--352 state the comparison
  conclusion: equal/proportional MPV families have their BNT blocks paired by a
  permutation with phases and invertible gauge matrices.
- `Papers/2011.12127/TN-Review-main.tex` lines 1846--1859 give the BNT definition
  and minimality characterization; lines 1864--1885 give the corresponding MPV
  expansion; lines 1891--1894 state the proportional-MPV matching conclusion.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 317--332 state the
  injectivity/Wielandt blocking step. This branch keeps that step as a hypothesis when
  invoking the overlap-rigidity theorem.

## Lean progress in this branch

### Equal-norm comparison file

New declarations:

- `MPSTensor.exists_bnt_sectorDecomp_pair_with_overlapSpan_of_commonPhaseCover`:
  given trace-preserving, primitive, irreducible, injective live block families with
  nonzero weights and common phase-cover data, construct sector decompositions whose
  bases satisfy `SectorBasisOverlapSpanHypotheses`.
- `MPSTensor.exists_bnt_sectorDecomp_pair_with_overlapSpan_of_proportionalDecompositionConclusion`:
  first turns a BNT proportional-decomposition conclusion into a common MPV phase cover,
  then applies the previous theorem.

These theorems discharge the `span_eq` field through `MPVCommonPhaseCover.span_eq`; no
finite-length span equality is assumed as input.

### `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`

New declarations:

- `MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_proportionalConclusion`:
  exact live decompositions at a common blocking period plus a BNT proportional-decomposition
  conclusion imply the sector-weight comparison theorem.
- `fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_proportionalConclusion_zeroTail`
  (in namespace `MPSTensor`): zero-tail equations at a common blocking period, equality
  of zero-tail dimensions, injectivity, and a BNT proportional-decomposition conclusion
  imply the zero-tail-aware sector comparison theorem.

The zero-tail theorem is the direct downstream consumer for the #989 data once the
physical-label compatibility theorem rewrites the common-length zero-tail equations with
the derived cyclic-sector live families and any needed injectivity refinement has been
supplied.

### Blueprint updates

`blueprint/src/chapter/ch11_assembly.tex` now records the two overlap-span consequences
and the two sector-comparison theorems. `blueprint/src/chapter/ch08_canonical.tex` now
points from the common-length cyclic-sector discussion to the zero-tail
proportional-decomposition theorem as the next checked comparison step.

## Remaining paper inputs

The branch deliberately leaves the following inputs explicit:

1. physical-label compatibility between the canonical blocked live tensor and the explicitly
   relabeled one-shot live tensor for the whole weighted family;
2. any additional common blocking required to make the final live sectors injective;
3. BNT proportional-decomposition data for those final common-length live-sector families,
   obtained from the exact live equality without assuming finite-length span equality.

Once these are supplied, the new zero-tail theorem produces the overlap-span data and
sector-weight conclusion through the common phase-cover route.
