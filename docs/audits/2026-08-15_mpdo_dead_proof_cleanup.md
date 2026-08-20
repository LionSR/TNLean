# MPDO/RFP exact-pass-through deletion audit

This audit records the public declarations removed by PR #6494 under the
repository-local exact-pass-through exception in
`docs/MATHLIB_style.md` §Deprecation. Every removed declaration has no
remaining non-Archive Lean consumer. The transfer-reindexing proof had one local
consumer, where it is now inlined as `hTransfer`; the other declarations had no
consumer before deletion. Each merely forwards to an existing theorem or
definition, exposes bundled witness data, or names a proof step now written
directly at its only use site.
The substantive component declarations remain public.

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.BNTLabelTheoremWitness.hasBNTLabelTheoremWitness` | Use `⟨W⟩`; `HasBNTLabelTheoremWitness data` is `Nonempty (BNTLabelTheoremWitness data)`. |
| `MPOTensor.BNTLabelTheoremWitness.ofChi_hasBNTLabelTheoremWitness` | Use `⟨BNTLabelTheoremWitness.ofChi ...⟩`. |
| `MPOTensor.RescalingStableLengthDependentRFP.oneLabelChi_matrix_eq_oneLabelChiMatrix2` | The equality is `rfl` from `oneLabelChiMatrix2`. |
| `MPOTensor.RescalingStableLengthDependentRFP.R_hasBNTAlgebraTensorClause` | Use `⟨R_oneLabelBNTAlgebraTensorClause⟩`. |
| `MPOTensor.RescalingStableLengthDependentRFP.doubledPhysTraceTransfer_reindexPhysical_oneSiteDoubledEquiv` | The proof is now the local `hTransfer` step inside `R_isSourceSimple`. |
| `MPSTensor.isLocallyOrthogonal_iff_isTransferIdempotent` | This is `Iff.rfl` from the definition of `IsLocallyOrthogonal`. |

## Follow-up deletions

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.BondTwoSingletonBaseModel.gaugeDeformedBaseMPO_algebraClause_canonicalForm_not_isMPDO` | Use `⟨gaugeDeformedBaseMPOBNTAlgebraTensorClause⟩`, `gaugeDeformedBaseMPO_toMPSTensor_isCPSVCanonicalForm`, and `gaugeDeformedBaseMPO_gauge_not_isMPDO`. |


## Retained transition APIs

Declarations that package several component results, transport a theorem through
a nontrivial step, or otherwise have independent public API content were retained
with dated deprecations instead of being deleted. This includes:

- `MPOTensor.PhysicalSectorFactorization.neighboringSupportInclusion_isometry`;
- `MPSTensor.transferMap_blockTensor_hasEigenvalue`;
- `MPOTensor.BondTwoSingletonBaseModel.baseMPO_hasBNTAlgebraTensorClause`;
- `MPOTensor.RescalingStableLengthDependentRFP.wMat_mulVec_eigVecs`;
- the eight `MPOTensor.HasBNTLabelTheoremWitness.exists_*` packaging theorems
  retained in `BNTTheoremWitnessConsequences`;
- `MPSTensor.duplicateScalarBlocks_counterexample`;
- `MPOTensor.RescalingStableLengthDependentRFP.R_isSourceSimple_and_not_isSimple`;
- `MPOTensor.SimpleVanishingCounterexample.M_isSimple_and_isSourceSimple_and_not_isNonvanishingSourceSimple`;
- `MPSTensor.bellPairChain_isTransferIdempotent_and_not_isPhysicalCID`;
- `MPOTensor.RescalingStableLengthDependentRFP.oneSiteDoubledEquiv_diagonal`,
  whose `@[simp]` behavior is part of the public automation API; and
- `MPSTensor.blockTransferSum_blockTransferSum`.

The old `TNLean.MPS.MPDO.BNTTheoremWitnessConsequences` import path is retained
as the module containing the deprecated witness-packaging APIs. The theorem
`MPOTensor.HasBNTLabelTheoremWitness.exists_source_chi_trace_equations`
was relocated to `BNTTheoremWitness` with its paper-facing source citation.

The physical-gauge conjunction wrapper
`MPOTensor.BondTwoSingletonBaseModel.gaugeDeformedBaseMPO_algebraClause_canonicalForm_not_isMPDO`
was initially retained because touching its
`BondTwoSingletonPhysicalGauge` module triggered the repository's 50-second
changed-module timing limit (62 seconds, then 52 seconds) despite successful full
Lean builds. PR #6504 placed the wrapper on a dated deprecation transition.
PR #6544 subsequently removed it; no Blueprint or docstring anchor used the
wrapper. Its three component replacements are
`MPOTensor.BondTwoSingletonBaseModel.gaugeDeformedBaseMPOBNTAlgebraTensorClause`,
`MPOTensor.BondTwoSingletonBaseModel.gaugeDeformedBaseMPO_toMPSTensor_isCPSVCanonicalForm`,
and
`MPOTensor.BondTwoSingletonBaseModel.gaugeDeformedBaseMPO_gauge_not_isMPDO`;
issue #6503 was closed by that deletion. The current development contains no
remaining Lean declaration, Blueprint anchor, or non-historical use of the
wrapper.

The chronology did not follow the ordinary compatibility interval: PR #6504
deprecated the wrapper on 2026-08-16, and PR #6544 deleted it on 2026-08-17.
The deletion PR did not expressly invoke the exact-pass-through exception, and
a post-merge changes-requested review identified that disclosure omission.
This audit records the process discrepancy without restoring the obsolete
conjunction.

Issue #6545 was closed as not a defect. PR #6551 verified that the
`InvariantProjection` import supplies the vertical-tensor multiplication
lemmas `verticalTensor_ketLeftMul` and `verticalTensor_braRightMul` used by the
physical-gauge proof, so the import is mathematically load-bearing rather than
obsolete.
