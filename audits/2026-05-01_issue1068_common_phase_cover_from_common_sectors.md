# Issue #1068 common-sector span consequence audit

## Scope

Issue #1068 asks for the step from the common-length cyclic-sector construction to
the finite-length nonzero-block span hypothesis used by the zero-tail sector
comparison theorem, or equivalently to common MPV phase-cover data for the two
nonzero-sector families.

The Lean theorem added in this round is
`MPSTensor.afterBlocking_commonSector_blockSpan_of_reindexedNonzeroParts`
in `TNLean/MPS/CanonicalForm/Assembly/ProportionalComparison.lean`.  It starts
from `SameMPV₂ A B` and the one-sided equality after relabeling blocked physical
words used by
`MPSTensor.afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`.
It then returns the common blocking length, the two zero-tail decompositions, the
weighted common-sector nonzero families, and their trace-preserving, primitive,
tensor-irreducible, positive-dimension, nonzero-weight, positive-length, and
length-zero conclusions.

For these exact common-sector families it records two conditional span
consequences:

- a common MPV phase cover gives the finite-length nonzero-block span equality by
  `MPSTensor.MPVCommonPhaseCover.span_eq`;
- a BNT proportional-decomposition conclusion gives the same span equality by
  `MPSTensor.mpv_span_eq_of_proportionalDecompositionConclusion`.

This is intentionally not an unconditional construction of the common phase
cover.  The theorem exposes the two remaining mathematical inputs: the
blocked-word coordinate equality tracked by #1075, and the final cross-side BNT
matching or common-phase comparison for the common-sector families.

## Relation to the paper proof

The paper-level comparison uses a basis of normal tensors and then pairs the
basis blocks by phase and gauge.  In the 2016 MPDO text this is stated in
`Papers/1606.00608/MPDO-22-12-17-2.tex:278--280` for the BNT characterization,
`350--352` for the proportional MPV theorem, and `355--357` for the equal-MPV
corollary.  The appendix proof gives the block pairing explicitly at
`Papers/1606.00608/MPDO-22-12-17-2.tex:1182`, where nonzero overlap identifies a
basis tensor and then Lemma `equalMPS` supplies the phase and gauge.  The review
version states the same chain at
`Papers/2011.12127/TN-Review-main.tex:1852--1854`, `1892--1894`, and
`1897--1900`.

The new theorem formalizes the bookkeeping immediately before that comparison:
after the common-length cyclic-sector construction has supplied the primitive
irreducible nonzero-sector families, a common phase cover or the BNT
proportional-decomposition data is exactly what is needed to obtain equality of
the finite-length MPV spans.

## Blueprint updates

The theorem is recorded in
`blueprint/src/chapter/ch11_assembly.tex` as
`thm:after_blocking_common_primitive_irreducible_blocks_block_span_consequences`.
The Ch. 8 open-direction remark now points to this theorem as the intermediate
span consequence between the common-sector decomposition and the zero-tail sector
comparison theorem.  The Ch. 11 equal-case remark states that this step remains
conditional on the common phase cover or proportional-decomposition comparison.

## Remaining inputs

To apply `MPSTensor.afterBlocking_sectorComparison_zeroTail_of_blockSpan` to the
common-sector output without an external span hypothesis, one still needs:

1. the blocked-word coordinate equality of #1075, or an equivalent theorem that
   supplies the `hReindexed` hypothesis for the weighted nonzero families;
2. a common MPV phase cover or a BNT proportional-decomposition conclusion for
   the chosen common-sector families;
3. the injectivity hypotheses for the common-sector blocks after any required
   further blocking;
4. the zero-tail dimension equality required by the zero-tail block-span theorem.

No periodic-blocking fundamental theorem from the Gemma route (arXiv:1708.00029) is used here.
