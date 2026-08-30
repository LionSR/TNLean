# LPDO proof-surface simplification

## Scope

This audit concerns the locally purifiable density-operator material associated
with CPSV16 Section 4.3 and the corrected fixed-parameter realization of
CPSV16 Example 4.10. It changes no mathematical statement from the paper, and
no surviving public Lean statement changes.

## Removed declarations and replacements

Two declarations had no remaining repository consumer and are removed:

- `MPOTensor.IsLPDO.exists_bipartitionedNormalizedMPO_eq_blockAncillaryTrace`
  is strictly subsumed by
  `MPOTensor.IsLPDO.exists_forall_bipartitionedNormalizedMPO_eq_blockAncillaryTrace`.
  The surviving theorem chooses one local purification and proves the same
  ancillary-trace identity simultaneously for every decomposition $N=L+K$.
- `MPOTensor.CommutingBondTraceMatrixObstruction.singletonPairEquiv` is the
  singleton instance of Mathlib's canonical finite-product equivalence and is
  replaced at both call sites by
  `(finProdFinEquiv (m := 1) (n := 1)).symm`.

A repository-wide search over Lean, Blueprint, documentation, scripts, papers,
and notes found no further occurrence of either removed name. The Blueprint
node `thm:lpdo_exists_block_channel_image`, which cited only the weaker first
theorem and had no consumer, is removed. The cut-uniform node remains the sole
Blueprint statement of the LPDO block-channel representation.

## Four-site purification calculation

The private four-site identity in `CPSVExample410Spectrum.lean` now uses
`MPOTensor.mpo_eq_purificationDensity`, the general propagation of a local
purification to every finite chain, rather than repeating the Kronecker-product
and trace expansion. Its statement and the ensuing Bell-diagonal and spectral
theorems are unchanged. The coefficient equality for the displayed
`purifier` and `pairEquiv` is definitional. The existential proposition
`CPSVExample410Operator.M_isLPDO` cannot recover those particular witnesses
definitionally, so no additional coefficient lemma or public API is introduced.

## Source and validation

The terminology and notation follow
`Papers/1606.00608/MPDO-22-12-17-2.tex:777--786,897--905`.
Targeted builds cover the three changed Lean modules and the direct
`CPSVExample410Entropy` consumer. The root build, generated-import check,
Blueprint synchronization and declaration checks, CPSV16 label audit,
reader-facing prose check, forbidden-token check, and `git diff --check` form
the final validation set.
