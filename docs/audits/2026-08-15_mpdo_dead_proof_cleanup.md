# MPDO/RFP exact-pass-through deletion audit

This audit records the public declarations removed by PR #6494 under the
repository-local exact-pass-through exception in
`docs/MATHLIB_style.md` §Deprecation. Every removed declaration had no
non-Archive Lean consumer. Each merely forwarded to an existing declaration,
exposed bundled witness data, packaged existing component theorems, or named a
proof step now written directly at its only use site. The substantive component
declarations remain public.

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.BNTLabelTheoremWitness.hasBNTLabelTheoremWitness` | Use `⟨W⟩`; `HasBNTLabelTheoremWitness data` is `Nonempty (BNTLabelTheoremWitness data)`. |
| `MPOTensor.BNTLabelTheoremWitness.ofChi_hasBNTLabelTheoremWitness` | Use `⟨BNTLabelTheoremWitness.ofChi ...⟩`. |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_source_predicates` | Unpack the witness and use `same_length_product_form`, `idempotent_coefficient_form`, `positive_chi_trace_power`, and `positive_chi_pos_entries`. |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_positive_length_coeff_eq_ofChi` | Unpack the witness and use `BNTLabelTheoremWitness.coeff_eq_ofChi_coeff`. |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_source_ofChi_predicates` | Unpack the witness and use `same_length_product_form_ofChi` and `idempotent_coefficient_form_ofChi`. |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_source_ofChi_equations` | Unpack the witness and use `same_length_product_eq_sum_ofChi` and `idempotent_eq_sum_ofChi`. |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_blocked_chi_pullback` | Unpack the witness and use `positiveBlockedChi_toDiagonal_of_pos`. |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_blocked_coefficient_comparison` | Unpack the witness and use `blocked_coeff_eq`. |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_blocked_coefficient_comparison_ofChi` | Unpack the witness and use `blocked_coeff_eq_ofChi`. |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_source_coefficient_equations` | Unpack the witness and use `same_length_product_eq_sum` and `idempotent_eq_sum`. |
| `MPSTensor.duplicateScalarBlocks_counterexample` | Use `duplicateScalarBlocks_isInjective`, `duplicateScalarBlocks_leftCanonical`, `duplicateScalarWeights_ne_zero`, `duplicateScalarBlocks_not_hasBiCF`, and `duplicateScalarBlocks_not_exists_linearIndependent_wordEntryFamily`. |
| `MPOTensor.RescalingStableLengthDependentRFP.oneLabelChi_matrix_eq_oneLabelChiMatrix2` | The equality is `rfl` from `oneLabelChiMatrix2`. |
| `MPOTensor.RescalingStableLengthDependentRFP.R_hasBNTAlgebraTensorClause` | Use `⟨R_oneLabelBNTAlgebraTensorClause⟩`. |
| `MPOTensor.RescalingStableLengthDependentRFP.R_isSourceSimple_and_not_isSimple` | Use `R_isSourceSimple` and `R_not_isSimple`. |
| `MPOTensor.RescalingStableLengthDependentRFP.oneSiteDoubledEquiv_diagonal` | Simplify directly with `oneSiteDoubledEquiv`. |
| `MPOTensor.RescalingStableLengthDependentRFP.doubledPhysTraceTransfer_reindexPhysical_oneSiteDoubledEquiv` | The proof is now the local `hTransfer` step inside `R_isSourceSimple`. |
| `MPSTensor.blockTransferSum_blockTransferSum` | Specialize `blockTransferSum_blockTransferSum_eq_smul` at scalar `1`. |
| `MPSTensor.bellPairChain_isTransferIdempotent_and_not_isPhysicalCID` | Use `bellPairChainTensor_isTransferIdempotent` and `bellPairChainTensor_not_isPhysicalCID`. |
| `MPSTensor.isLocallyOrthogonal_iff_isTransferIdempotent` | This is `Iff.rfl` from the definition of `IsLocallyOrthogonal`. |

The public theorem
`MPOTensor.PhysicalSectorFactorization.neighboringSupportInclusion_isometry`
was not deleted because its proof has independent mathematical content. It is
retained with a dated deprecation transition. Likewise, unused declarations
whose proofs or definitions were not exact pass-throughs remain in the library.
