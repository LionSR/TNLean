# 2026-04-29 — Issue #944 overlap-span from common nonzero-sector comparison

## Scope and issue-thread check

This branch continues the non-Gemma canonical-form equal-case path after merged PRs #987,
#988, and #989. The current issue-thread state is:

- #944 has reduced the collapsed-BNT representative obligation to the finite-length span
  equality for the two nonzero-weight block families.
- #970 has the common phase-cover span mechanism and the BNT proportional-decomposition
  comparison route on `main`.
- #942/#969/#989 provide common physical blocking length and relabeled cyclic-sector families
  with zero-tail bookkeeping, while leaving the identification of the two blocked-word descriptions,
  injectivity/Wielandt refinement, and final BNT comparison data explicit.
- #652 remains the umbrella for closing the non-periodic CPSV/CPGSV equal-case
  canonical-form theorem from `SameMPV₂`.

The new theorems therefore do not assert that arbitrary `SameMPV₂ A B` already gives the
final span equality. Instead they compose the available common-cover and BNT comparison
machinery with the exact nonzero-part and zero-tail sector comparison theorems, making the
remaining hypotheses precise.

## Paper/source references

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
  given trace-preserving, primitive, irreducible, injective block families with nonzero
  weights and common phase-cover data, construct sector decompositions whose bases
  satisfy `SectorBasisOverlapSpanHypotheses`.
- `exists_bnt_sectorDecomp_pair_with_overlapSpan_of_proportionalDecompositionConclusion`
  (in namespace `MPSTensor`): first turns BNT proportional-decomposition data into a
  common MPV phase cover, then applies the previous theorem.
- `mpv_span_eq_of_proportionalDecompositionConclusion` (in namespace `MPSTensor`):
  exposes the finite-length MPV span equality obtained from the same proportional
  comparison.
- `mpv_span_eq_of_separated_normalCFBNT_data` (in namespace `MPSTensor`): combines
  separated normal canonical-form data with the BNT comparison theorem to obtain the
  same finite-length span equality.

These theorems discharge the `span_eq` field through `MPVCommonPhaseCover.span_eq`; no
finite-length span equality is assumed as a hypothesis in the common-cover and
proportional-decomposition routes.

### BNT proportional comparison assembly file

New declarations:

- `MPSTensor.afterBlocking_sectorComparison_of_proportionalDecompositionConclusion`:
  exact nonzero-part decompositions at a common blocking period plus BNT
  proportional-decomposition data imply the sector-weight comparison theorem.
- `afterBlocking_sectorComparison_zeroTail_of_blockSpan` (in namespace `MPSTensor`):
  zero-tail equations at a common blocking period, equality of zero-tail dimensions,
  injectivity, and finite-length nonzero-block span equality imply the zero-tail-aware
  sector comparison theorem.
- `afterBlocking_sectorComparison_zeroTail_of_commonPhaseCover` (in namespace
  `MPSTensor`): obtains the previous span hypothesis from common MPV phase-cover data.
- `afterBlocking_sectorComparison_zeroTail_of_proportionalDecompositionConclusion`
  (in namespace `MPSTensor`): obtains the common MPV phase-cover data from BNT
  proportional-decomposition data and applies the common-cover zero-tail theorem.

These zero-tail theorems are the direct mathematical consequence for the #989 data once a
theorem identifies the canonical blocked nonzero part with the relabeled cyclic-sector
description in the common blocked alphabet and any needed injectivity refinement has been
supplied.

### Blueprint updates

`blueprint/src/chapter/ch11_assembly.tex` now records the overlap-span consequences,
the direct span-equality corollaries, and the sector-comparison theorems. The zero-tail
entries are split into block-span, common-cover, and proportional-decomposition forms so
downstream arguments can cite exactly the hypothesis they have.
`blueprint/src/chapter/ch08_canonical.tex` continues to point from the common-length
cyclic-sector discussion to the zero-tail
proportional-decomposition theorem as the next checked comparison step.

## Remaining paper hypotheses

The branch deliberately leaves the following hypotheses explicit:

1. agreement, as MPV families, between the canonical blocked nonzero part and the
   relabeled cyclic-sector tensor for the whole weighted family;
2. any additional common blocking required to make the final nonzero sectors injective;
3. BNT proportional-decomposition data for those final common-length nonzero-sector families,
   obtained from the exact nonzero-part equality without assuming finite-length span equality.

Once these are supplied, the new zero-tail theorem produces the overlap-span data and
sector-weight conclusion through the common phase-cover route.

## 2026-05-01 update: common primitive sector hypotheses

After the common primitive and common-length sector theorems from Wave 23, the
zero-tail sector comparison can be stated one step closer to the canonical-form
reduction.  The new structure
`MPSTensor.CommonPrimitiveSpanHypotheses` records precisely the remaining
conditions on the common primitive nonzero-sector families: equality of the two
zero-tail dimensions, one-site injectivity of the sector blocks, and equality of
the finite-length MPV spans.  The helper
`MPSTensor.CommonPrimitiveSpanHypotheses.of_commonPhaseCover` fills the span field
from a common MPV phase cover.

The theorem
`MPSTensor.afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_spanHypotheses`
then composes the conditional common primitive theorem
`MPSTensor.afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`
with the zero-tail block-span comparison.  It does not construct the blocked-word
coordinate equality or the common phase cover.  Instead, it consumes exactly the
mathematical assertions expected from those neighboring steps: the reindexing of
blocked physical words, equal zero tails, injectivity, and either span equality
or common phase-cover data for the produced common primitive sector families.

This remains aligned with the paper references listed above.  The BNT comparison
and phase matching are the steps described in `Papers/1606.00608/MPDO-22-12-17-2.tex`
lines 271--302 and 349--352, while the injectivity/Wielandt blocking requirement
is the passage in lines 317--332.  In the review article, the corresponding BNT
comparison is `Papers/2011.12127/TN-Review-main.tex` lines 1846--1859,
1864--1885, and 1891--1894.

## 2026-05-07 update: unconditional primitive block variants and gap documentation

The `OverlapSpanComparison.lean` module now includes a detailed doc-block enumerating
the remaining paper-source gaps that prevent an unconditional derivation of
`SectorBasisOverlapSpanHypotheses` from the structural data alone:

1. **One-site injectivity** — not derivable from the structural theorem; requires
   a further Wielandt-type blocking (paper lines 317--332, arXiv:1606.00608).

2. **Finite-length MPV span equality** — requires the BNT comparison and
   proportional-decomposition data (paper lines 271--302, 349--352).

3. **Phase-gauge matching data** — requires normal canonical form, strict weight
   ordering, gauge-phase separation, and proportional decomposition data
   (packaged as `CommonPrimitiveBNTCoverHypotheses`).

New unconditional (hReindexed-free) theorem variants added at the end of the file:

- `sectorBasisOverlapSpanHypotheses_of_unconditionalPrimitiveBlocks`
- `sectorBasisOverlapSpanHypotheses_of_unconditionalPrimitiveBlocks_commonPhaseCover`
- `sectorBasisOverlapSpanHypotheses_of_unconditionalPrimitiveBlocks_bntCover`
- `sectorBasisOverlapSpanHypotheses_of_unconditionalPrimitiveBlocks_commonPrimitiveBNTData`
- `sectorBasisOverlapSpanHypotheses_of_unconditionalPrimitiveBlocks_proportional`

These theorems use `unconditional_commonPrimitiveIrreducibleBlocks` (which needs no
`CommonSectorRelabelingHypothesis`) instead of
`afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`.
All remaining hypotheses (injectivity, span equality, BNT comparison) remain
explicitly conditional — consistent with the paper gap analysis.

The gap is genuine and not an artifact of the formalization: injectivity requires
a separate Wielandt blocking step beyond period removal, and span equality requires
the BNT comparison theorem with normal canonical-form and proportional-decomposition
data. These are both substantive paper-level arguments that have not yet been
formalized in the project.
