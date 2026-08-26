# Nonzero-coefficient convention for CPSV canonical forms

This audit records the convention adopted by PR #6963 and the public
declarations that the convention made redundant. It is the audit note required
by `docs/project_conventions.md` §Style for removals under the pass-through
exception, extended to the mathematical-language renames of
`docs/CONTRIBUTING.md` §Mathematical-language renames. No compatibility alias is
provided for any renamed or removed declaration.

## The convention

CPSV16 (arXiv:1606.00608) writes a canonical form as a weighted direct sum
$\bigoplus_k \mu_k A_k$ of normal blocks (eq. `II_CF1`, lines 237--244) and
normalizes the weights at line 246 so that the largest modulus is one. The
formalization previously allowed $\mu_k = 0$ in `CPSVCanonicalFormData` and
carried a parallel "active block" theory: a subtype `data.Active` of the block
indices with nonzero weight, an "active" basis-of-normal-tensors presentation,
and a family of refutations showing that the printed statements of
Proposition 2.7, Theorem 2.10, Corollary 2.11, Corollary 3.12, Lemma A.5,
and Corollary A.6 fail when a zero-weight block is adjoined.

The convention now in force is that every canonical-form coefficient is
nonzero: `CPSVCanonicalFormData` carries the field
`weights_ne_zero : ∀ k, weights k ≠ 0`, the sector decompositions used by the
BNT fundamental theorem already have nonzero copy weights, and every theorem
that previously quantified over `data.Active` quantifies over `Fin data.r`.
A zero-weight summand is invisible to every positive-length matrix-product
vector, so nothing is lost by excluding it, and the source statements listed
above become theorems under this reading. The convention is recorded for the
paper-facing side in `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`
and cited from the affected theorems by a one-line
`**Local fix (nonzero coefficients):**` marker.

Owner decisions that shaped the pass:

- the literal `MPSTensor.IsCPSVBasisOfNormalTensors` stays as the
  Definition 2.4 interface; the grouped presentation predicate is now
  `MPSTensor.IsBNTSectorPresentation`;
- the three Chapter 11 printed-status nodes for Theorem 2.10, Corollary 2.11,
  and Corollary A.6 were deleted and the label-audit rows repointed to the
  surviving theorems;
- `TNLean/MPS/FundamentalTheorem/SectorBNT/CanonicalFormEqual.lean` was deleted;
- the historical power-sum note
  `docs/paper-gaps/cpsv16_power_sum_alternative_route.tex` was kept.

The MPDO inverse-map "active sector" vocabulary
(`MPOTensor.PhysicalSectorFactorization.ActiveSector`, `ActiveSector*`,
`CyclicActive*`, `activeSectorTraceMatrix`, `Inactive` in
`PhysicalSectorActiveRestriction.lean`, `inactive*Density`,
`zeroRightTensorOnInactive`) is a different concept (zero right tensors in
the Case-I factorization) and is untouched, as is the `ActiveLabel` corner
vocabulary of `TNLean/MPS/MPDO/VerticalProductSpectralFamily.lean`.

## Deleted modules

| Module | Disposition |
|---|---|
| `TNLean/MPS/CanonicalForm/ActiveBlocks.lean` | Deleted; the active-block restriction is the identity under the convention. |
| `TNLean/MPS/CanonicalForm/ActiveBNTRefinement.lean` | Replaced by `TNLean/MPS/CanonicalForm/BNTRefinement.lean`. |
| `TNLean/MPS/CanonicalForm/BNTUniqueness.lean` | Deleted; its refutation adjoined a zero-weight block. |
| `TNLean/MPS/FundamentalTheorem/SectorBNT/CanonicalFormEqual.lean` | Deleted; `CanonicalFormEqualAmbient.lean` is the Corollary 2.11 statement. |
| `TNLean/MPS/MPU/ActiveTransferMultiplicity.lean` | Replaced by `TNLean/MPS/MPU/TransferMultiplicity.lean`. |
| `TNLean/MPS/RFP/BNTResidualIsometryCounterexample.lean` | Deleted; its refutation adjoined an unused normal tensor with zero coefficient. |

## Removed declarations

Every removed declaration either expressed the active-block restriction
(now the identity), was a refutation that depended on a zero-weight block, or
was a pass-through to a declaration that survives under a new name. All
non-`Archive` consumers were migrated in the same PR; no blueprint `\lean{}`
tag cites an old name.

### `CPSVCanonicalFormData` active-block structure

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.CPSVCanonicalFormData.Active` | `Fin data.r`; every block has nonzero weight by `data.weights_ne_zero`. |
| `MPSTensor.CPSVCanonicalFormData.Inactive` | None; the subtype is empty under the convention. |
| `MPSTensor.CPSVCanonicalFormData.activeEquiv` | None; the index type is `Fin data.r` itself. |
| `MPSTensor.CPSVCanonicalFormData.activeDim` | `data.dim`. |
| `MPSTensor.CPSVCanonicalFormData.activeWeight` | `data.weights`. |
| `MPSTensor.CPSVCanonicalFormData.activeBlocks` | `data.blocks`. |
| `MPSTensor.CPSVCanonicalFormData.sameMPV₂Pos_toTensorFromBlocks_active` | `data.reconstruct` together with `SameMPV₂Pos` of the unrestricted block family. |
| `MPSTensor.CPSVCanonicalFormData.sameMPV₂Pos_activeBlocks` | `data.reconstruct`. |
| `MPSTensor.CPSVCanonicalFormData.activeCoordinateMap` | None; the coordinate map is the identity. |
| `MPSTensor.CPSVCanonicalFormData.activeCoordinateMap_injective` | None. |
| `MPSTensor.CPSVCanonicalFormData.activeCoordinateMap_finSigmaFinEquiv` | None; the coordinate map is the identity. |
| `MPSTensor.CPSVCanonicalFormData.activeCoordinateCoisometry` | `data.ambient_coisometry`. |
| `MPSTensor.CPSVCanonicalFormData.activeCoordinateCoisometry_mul_conjTranspose` | `data.coisometric`. |
| `MPSTensor.CPSVCanonicalFormData.activeCoordinateCoisometry_apply` | None. |
| `MPSTensor.CPSVCanonicalFormData.toTensorFromBlocks_active_eq_submatrix` | None; there is no proper active submatrix. |
| `MPSTensor.CPSVCanonicalFormData.exact_active_reconstruction` | `data.reconstruct` (the exact reconstruction is the defining field). |
| `MPSTensor.CPSVCanonicalFormData.activeEquivBlockTensor` | None; `blockTensor` already acts on `Fin data.r`. |
| `MPSTensor.CPSVCanonicalFormData.sum_activeRepresentative_dim_le` | `MPSTensor.CPSVCanonicalFormData.sum_representative_dim_le`. |

Private helpers removed with `ActiveBlocks.lean`: `Matrix.rowSelection`,
`Matrix.rowSelection_apply`, `Matrix.rowSelection_mul_conjTranspose`,
`Matrix.eq_conjTranspose_rowSelection_mul_submatrix_mul_rowSelection`,
`activeCoordinateEmbedding`, `weight_eq_zero_of_coordinate_not_active`,
`toTensorFromBlocks_row_outside_active_eq_zero`,
`toTensorFromBlocks_col_outside_active_eq_zero`.

### BNT sector presentation and refinement

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.IsActiveCPSVBasisOfNormalTensors` | `MPSTensor.IsBNTSectorPresentation`. |
| `MPSTensor.IsActiveCPSVBasisOfNormalTensors.isCPSVBasisOfNormalTensors` | `MPSTensor.IsBNTSectorPresentation.isCPSVBasisOfNormalTensors`. |
| `MPSTensor.IsActiveCPSVBasisOfNormalTensors.blocks_not_gaugePhaseEquiv` | `MPSTensor.IsBNTSectorPresentation.blocks_not_gaugePhaseEquiv`. |
| `MPSTensor.IsActiveCPSVBasisOfNormalTensors.of_sameMPV₂Pos` | `MPSTensor.IsBNTSectorPresentation.of_sameMPV₂Pos`. |
| `MPSTensor.IsActiveCPSVBasisOfNormalTensors.exists_pos_mpvState_ne_zero` | `MPSTensor.IsBNTSectorPresentation.exists_pos_mpvState_ne_zero`. |
| `MPSTensor.IsActiveCPSVBasisOfNormalTensors.smul_left` | `MPSTensor.IsBNTSectorPresentation.smul_left`. |
| `MPSTensor.IsActiveCPSVBasisOfNormalTensors.equiv_of_sameMPV₂Pos` | `MPSTensor.IsBNTSectorPresentation.equiv_of_sameMPV₂Pos`. |
| `MPSTensor.CPSVCanonicalFormData.activePhaseClasses` | `MPSTensor.CPSVCanonicalFormData.phaseClasses`. |
| `MPSTensor.CPSVCanonicalFormData.activeClassCopyEquiv` | `MPSTensor.CPSVCanonicalFormData.classCopyEquiv` (now `phaseClasses.enumEquiv`). |
| `MPSTensor.CPSVCanonicalFormData.activeClassCopyEquiv_apply` | `MPSTensor.CPSVCanonicalFormData.classCopyEquiv_apply`. |
| `MPSTensor.CPSVCanonicalFormData.activeRepresentativeIndex` | `MPSTensor.CPSVCanonicalFormData.representativeIndex`. |
| `MPSTensor.CPSVCanonicalFormData.activeClassCopy` | `MPSTensor.CPSVCanonicalFormData.classCopy`. |
| `MPSTensor.CPSVCanonicalFormData.activeClassCopy_activeClassCopyEquiv` | `MPSTensor.CPSVCanonicalFormData.classCopy_classCopyEquiv`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement` (fields `regroupedBlocksEq`, `copy`; indexed by `Fin data.r`). |
| `MPSTensor.CPSVCanonicalFormData.groupedIndexEquiv` | None; `GroupedIndex` no longer has an inactive summand. |
| `MPSTensor.CPSVCanonicalFormData.groupedIndexEquiv_inl` | None. |
| `MPSTensor.CPSVCanonicalFormData.groupedIndexEquiv_inr` | None. |
| `MPSTensor.CPSVCanonicalFormData.groupedListedEquiv_activeCopy` | `MPSTensor.CPSVCanonicalFormData.groupedListedEquiv_groupedPosition`, itself retired unused on 2026-08-26 (see `2026-08-26_canonical_form_retirements.md`). |
| `MPSTensor.CPSVCanonicalFormData.groupedListedEquiv_inactive` | None. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.groupedWeight` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.groupedWeight`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.groupedBlocks` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.groupedBlocks`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.groupedTensor` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.groupedTensor`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.groupedWeight_activeCopy` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.groupedWeight_copy`, itself retired unused on 2026-08-26 (see `2026-08-26_canonical_form_retirements.md`). |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.groupedWeight_inactive` | None. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.regroupedTensor_eq_groupedTensor` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.regroupedTensor_eq_groupedTensor`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.groupedRegroupLetterwise` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.groupedRegroupLetterwise`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.reconstructGrouped` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.reconstructGrouped`. |
| `MPSTensor.CPSVCanonicalFormData.exists_activeBNTRefinement` | `MPSTensor.CPSVCanonicalFormData.exists_bntRefinement`. |
| `MPSTensor.CPSVCanonicalFormData.activeBNTRefinement` | `MPSTensor.CPSVCanonicalFormData.bntRefinement`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.activeCopy` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.copy`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.representativeSectorDecomposition` and its five `_basisCount`, `_basisDim`, `_basis`, `_copies`, `_weight` lemmas | The same names under `MPSTensor.CPSVCanonicalFormData.BNTRefinement`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.groupedTensor_sameMPV₂Pos_representativeSectorDecomposition` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.groupedTensor_sameMPV₂Pos_representativeSectorDecomposition`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.groupedTensor_isActiveCPSVBasisOfNormalTensors` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.groupedTensor_isBNTSectorPresentation` (hypothesis `0 < data.r` instead of `Nonempty data.Active`). |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.source_sameMPV₂Pos_groupedTensor` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.source_sameMPV₂Pos_groupedTensor`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.isActiveCPSVBasisOfNormalTensors` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.isBNTSectorPresentation` (hypothesis `0 < data.r`). |
| `MPSTensor.CPSVCanonicalFormData.BNTRefinement.groupedMarkedBlocks_active` (MPDO representative grouped Lemma L) | `groupedMarkedBlocks` now has a single branch; unfold it directly. |

### BNT characterization and uniqueness

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal` (old public wrapper with a guarded coverage clause `weights k ≠ 0 → ...`) | The same name, formerly the private `isCPSVBasisOfNormalTensors_iff_active_blocks_covered_and_minimal`, now public with hypothesis `(hμne : ∀ k, μ k ≠ 0)` and an unguarded coverage clause. |
| `MPSTensor.CPSVCanonicalFormData.isCPSVBasisOfNormalTensors_iff_covered_and_minimal` (guarded form) | Same name; the `weights k ≠ 0 →` antecedent is dropped and discharged by `data.weights_ne_zero`. |
| `MPSTensor.exists_isCPSVBasisOfNormalTensors_unequal_card` | None; the refutation adjoined a zero-coefficient block, which the convention excludes. |
| `MPSTensor.IsCPSVBasisOfNormalTensors.equiv_of_converse_coverage` | `MPSTensor.IsBNTSectorPresentation.equiv_of_sameMPV₂Pos`; converse coverage is automatic. |

Private helpers removed with `BNTUniqueness.lean`: `symbolTensor`,
`symbolTensor_transferMap`, `symbolTensor_isNormalTensor`,
`symbolTensor_mpv_self`, `symbolTensor_mpv_other`,
`symbolTensor_pair_linearIndependent`, `singletonSymbolFamily`,
`pairSymbolFamily`, `singletonSymbolFamily_isCPSVBasisOfNormalTensors`,
`pairSymbolFamily_isCPSVBasisOfNormalTensors`.

### Sector BNT bridge and equal-MPV theorems

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.CPSVCanonicalFormData.exists_active_isBNTCanonicalForm` | `MPSTensor.CPSVCanonicalFormData.exists_isBNTCanonicalForm` (conclusion `P.totalDim = ∑ k, data.dim k`). |
| `MPSTensor.CPSVCanonicalFormData.exists_active_isBNTCanonicalForm_exact` | `MPSTensor.CPSVCanonicalFormData.exists_isBNTCanonicalForm_exact`. |
| `MPSTensor.CPSVCanonicalFormData.exists_active_fundamentalTheorem_equal_canonicalForm` | `MPSTensor.fundamentalTheorem_equal_canonicalForm` through `exists_isBNTCanonicalForm`; see `CanonicalFormEqualAmbient.lean`. |
| `MPSTensor.CPSVCanonicalFormData.exists_active_fundamentalTheorem_equal_canonicalForm_unitary` | `MPSTensor.fundamentalTheorem_equal_canonicalForm_unitary` through `exists_isBNTCanonicalForm`; see `CanonicalFormEqualAmbient.lean`. |

### MPU canonical form and transfer multiplicity

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.CPSVCanonicalFormData.HasFullActiveSupport` | `MPSTensor.CPSVCanonicalFormData.HasFullSupport` (`∑ k, data.dim k = D`). |
| `MPSTensor.CPSVCanonicalFormData.hasFullActiveSupport_blockTensor` | `MPSTensor.CPSVCanonicalFormData.hasFullSupport_blockTensor`. |
| `MPSTensor.CPSVCanonicalFormData.hasFullActiveSupport_reindexPhysical` | `MPSTensor.CPSVCanonicalFormData.hasFullSupport_reindexPhysical`. |
| `hasFullActiveSupport_castCFIIData` (private) | `hasFullSupport_castCFIIData` (private). |
| `hasFullActiveSupport_normalizedDiagonalLiftCFIIData` | `hasFullSupport_normalizedDiagonalLiftCFIIData`. |
| `hasFullActiveSupport_tensorPhysicalIdCFIIData` | `hasFullSupport_tensorPhysicalIdCFIIData`. |
| `hasFullActiveSupport_physicalAdjointNormalizedFlattening` | `hasFullSupport_physicalAdjointNormalizedFlattening`. |
| `not_hasFullActiveSupport` (source-V counterexample) | `not_hasFullSupport`. |
| `MPSTensor.CPSVCanonicalFormData.isIrreducibleTensor_of_active_dim_eq` | `MPSTensor.CPSVCanonicalFormData.isIrreducibleTensor_of_dim_eq` (the `weights k ≠ 0` argument is dropped). |
| `MPSTensor.CPSVCanonicalFormData.active_dim_eq_of_card_active_eq_one_of_fullActiveSupport` | `MPSTensor.CPSVCanonicalFormData.dim_eq_of_r_eq_one_of_fullSupport`. |
| `MPSTensor.CPSVCanonicalFormData.isIrreducibleTensor_of_card_active_eq_one_of_fullActiveSupport` | `MPSTensor.CPSVCanonicalFormData.isIrreducibleTensor_of_r_eq_one_of_fullSupport`. |
| `MPSTensor.CPSVCanonicalFormData.isNormalTensor_of_card_active_eq_one_of_fullActiveSupport` | `MPSTensor.CPSVCanonicalFormData.isNormalTensor_of_r_eq_one_of_fullSupport`. |
| `MPSTensor.CPSVCanonicalFormData.activeTransferEigenvalue` | `MPSTensor.CPSVCanonicalFormData.transferEigenvalue`. |
| `MPSTensor.CPSVCanonicalFormData.activeTransferEigenvalue_eq_one` | `MPSTensor.CPSVCanonicalFormData.transferEigenvalue_eq_one`. |
| `MPSTensor.CPSVCanonicalFormData.card_active_eq_one_of_shifted_transfer_trace` | `MPSTensor.CPSVCanonicalFormData.r_eq_one_of_shifted_transfer_trace` (conclusion `data.r = 1`). |

Private helpers renamed with `TransferMultiplicity.lean`:
`ambientActiveVector` became `ambientFixedVector` (with the `_ne`,
`transferMap_`, `transferMap_…_eq_self`, and `linearIndependent_` lemmas
following), and `activeTransferEigenvalue_ne` became `transferEigenvalue_ne`.

### Renormalization fixed points

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.CPSVCanonicalFormData.active_weight_norm_one_and_block_rfp` | `MPSTensor.CPSVCanonicalFormData.weight_norm_one_and_block_rfp`. |
| `MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement.exists_residualIsometryFamily_of_isTransferIdempotent` | `MPSTensor.CPSVCanonicalFormData.BNTRefinement.exists_residualIsometryFamily_of_isTransferIdempotent`. |
| `MPSTensor.IsCPSVCanonicalForm.exists_activeBNT_residualIsometryFamily_of_isTransferIdempotent` | `MPSTensor.IsCPSVCanonicalForm.exists_bntRefinement_residualIsometryFamily_of_isTransferIdempotent`. |
| `MPSTensor.cpsvCorollary312_arbitraryBNT_counterexample` | None; the refutation adjoined an unused normal tensor with zero coefficient. |
| `MPSTensor.corollary312BondDim`, `MPSTensor.corollary312Tensor`, `MPSTensor.corollary312UnusedTensor`, `MPSTensor.corollary312CandidateFamily` | None (only consumed by the deleted counterexample). |

Private helpers removed with `BNTResidualIsometryCounterexample.lean`:
`invSqrtTwo_mul_self`, `corollary312Tensor_transferMap`,
`corollary312Tensor_isNormalTensor`, `corollary312Tensor_isTransferIdempotent`,
`corollary312Tensor_mpv_one`, `corollary312Tensor_mpv_zero`,
`corollary312UnusedTensor_transferMap`,
`corollary312UnusedTensor_isNormalTensor`,
`corollary312UnusedTensor_mpv_const`,
`corollary312CandidateFamily_linearIndependent`,
`corollary312Tensor_isCPSVCanonicalForm`,
`corollary312Tensor_isCPSVBasisOfNormalTensors`,
`corollary312CandidateFamily_not_residual`,
`corollary312CandidateFamily_no_residual_decomposition`.

### MPDO simplicity

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.activeBNT_basis_not_isNilpotent_iff` | `MPOTensor.bnt_basis_not_isNilpotent_iff`. |
| `MPOTensor.SimpleVanishingCounterexample.M_isSimple_and_isSourceSimple_and_not_isNonvanishingSourceSimple` (deprecated) | `M_isSimple`, `M_isSourceSimple`, `M_not_isNonvanishingSourceSimple`. |

`MPOTensor.IsSourceSimple` now quantifies over `IsBNTSectorPresentation`;
its statement is otherwise unchanged.

## Signature changes without renames

| Declaration | Change |
|---|---|
| `MPSTensor.CPSVCanonicalFormData` | New field `weights_ne_zero : ∀ k, weights k ≠ 0` (source lines 214--225, 246). |
| `MPSTensor.CPSVCanonicalFormData.ofBlocks` | New argument `(weights_ne_zero : ∀ k, weights k ≠ 0)` after `weights`. |
| `MPSTensor.CPSVCanonicalFormData.isCPSVBasisOfNormalTensors_iff_covered_and_minimal` | Coverage clause no longer guarded by `weights k ≠ 0`. |
| `MPSTensor.CPSVCanonicalFormData.isIrreducibleTensor_of_dim_eq` | The `weights k ≠ 0` argument is dropped. |
| `MPSTensor.CPSVCanonicalFormData.exists_isBNTCanonicalForm` and `_exact` | Conclusion `P.totalDim = ∑ k, data.dim k` instead of the active sum. |
| `MPSTensor.cubePhaseWeight_ne_zero` | New theorem (RFP phase oscillation), used to construct the cube-phase canonical-form data. |

## Blueprint nodes deleted

`thm:cpsv_remove_zero_weight_blocks`, `thm:cpsv_canonical_form_active_blocks`,
`thm:cpsv_exact_active_reconstruction`, `thm:cpsv_active_core_equal_ft`,
`thm:cpsv_active_core_equal_ft_unitary`,
`thm:cpsv_bnt_uniqueness_counterexample`,
`thm:cpsv_bnt_uniqueness_converse_coverage`,
`def:mpu_active_blocks_blocking_equiv`, `thm:cpsv_prop27_printed_status`,
`lem:cpsv_power_sum_printed_status`, `thm:cpsv_theorem210_printed_status`,
`cor:cpsv_corollary211_printed_status`, `cor:cpsv_corollary_a6_printed_status`,
`cor:cpsv_iii_cor3_status`, `thm:cpsv_cor312_arbitrary_bnt_counterexample`.
The source-anchor comments of the printed-status nodes now sit on the
surviving theorems, and `docs/audits/data/cpsv16-label-dispositions.tsv`
records each affected source label as formalized under the nonzero-coefficient
local correction.

## Paper-gap notes

`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` was rewritten
as the convention record; `cpsv16_bnt_characterization_active_blocks.tex` was
deleted and its Figure 11 display moved into
`cpsv16_figure11_per_pair_support.tex`. The notes
`cpsv16_rfp_isometry_scope.tex`, `cpsv16_simple_tensor_nilpotency.tex`,
`cpsv16_unit_weight_rfp_scale_tension.tex`, `cpgsv17_vertical_cf_grouping.tex`,
`mpu_canonical_form_full_support.tex`, `tnlean_bnt_ft_theorem_surface.tex`,
`cpsv16_bnt_rate_quantification.tex`,
`cpsv16_nondominant_per_block_projection.tex`,
`cpsv16_fixed_block_cancellation.tex`, and
`cpsv16_two_layer_sector_refinement.tex` were updated to the new names and no
longer assert that the printed statements are false.
