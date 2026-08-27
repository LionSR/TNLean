# MPDO zero-reference and pass-through cleanup (2026-08-26)

This audit records a slice of the open proof-debt ledger entry S2
(`docs/proof_debt_ledger.md`, issue #4564): declarations under
`TNLean/MPS/MPDO/` that either had no consumer at all or merely forwarded to a
theorem stated one abstraction layer down. The removals use the
repository-local pass-through exception of `docs/project_conventions.md`
§Style, so no transition declaration is left behind. At the audited head each
removed name had no non-`Archive` consumer, and every Blueprint `\lean{...}`
tag naming one was redirected to its survivor in the same change.

## Removed declarations

| Removed | Replacement |
|---|---|
| `MPOTensor.reindex_product_embedLocalOperator_two_of_etaPair_decomposition` (`TNLean/MPS/MPDO/CommutingBondEtaCyclicCore.lean`) | `MPOTensor.reindex_product_embedLocalOperator_of_etaPair_decomposition` in the same file, instantiated at `N := 2` with `(by omega : 2 ≤ 2)`. The removed theorem's whole body was that instantiation. |
| `MPOTensor.RescalingStableLengthDependentRFP.oneLabelChiScaled_posEntries` (`TNLean/MPS/MPDO/RescalingStableLengthDependentRFP.lean`) | None. The lemma had no consumer and no Blueprint `\lean{}` tag. Its sibling `oneLabelChi_posEntries` is deliberately retained: it is consumed at `TNLean/MPS/MPDO/RescalingStableChiUniformity.lean:138`. |
| `MPOTensor.BNTFusionTensorClause.projectorQBlock` (`TNLean/MPS/MPDO/TopologicalProjectors.lean`) | `MPOTensor.BNTFusionCoisometryFamily.projectorQBlock`, reached from a clause by `H.toBNTFusionCoisometryFamily`. |
| `MPOTensor.BNTFusionTensorClause.fusionCoisometry_mul_physTraceTransfer_mul_conjTranspose` | `MPOTensor.BNTFusionCoisometryFamily.fusionCoisometry_mul_physTraceTransfer_mul_conjTranspose` at `H.toBNTFusionCoisometryFamily`. |
| `MPOTensor.BNTFusionTensorClause.projectorQBlock_isStarProjection` | `MPOTensor.BNTFusionCoisometryFamily.projectorQBlock_isStarProjection` at `H.toBNTFusionCoisometryFamily`, with the coefficient family `BNTLabelCoefficientFamily.ofChi H.chi` and its positive-length trace-power form. |
| `MPOTensor.BNTFusionTensorClause.conjugatedProjectorQBlock` | `MPOTensor.BNTFusionCoisometryFamily.conjugatedProjectorQBlock` at `H.toBNTFusionCoisometryFamily`. |
| `MPOTensor.BNTFusionTensorClause.conjugatedProjectorQBlock_isOrthogonalProjection` | `MPOTensor.BNTFusionCoisometryFamily.conjugatedProjectorQBlock_isOrthogonalProjection` at `H.toBNTFusionCoisometryFamily`, same coefficient-family arguments. |
| `MPOTensor.EtaLocalStructureData.exists_unitary_blockActions_of_pairBond` (`TNLean/MPS/MPDO/CommutingFormSpatialBridge.lean`) | `MPOTensor.TranslationInvariantBondData.exists_unitary_blockActions_of_pairBond` in the same file, reached by `data.bondData`. The removed theorem's whole body was that projection. |
| `MPOTensor.physCloseN_three_apply` (`TNLean/MPS/MPDO/PhysicalClosure.lean`) | None needed. The flat-coordinate (`Fin 3 -> Fin d`) restatement of `MPOTensor.physCloseN_apply` at `N = 3`; its whole proof was `simp [physCloseN, List.ofFn_succ, evalWord_cons, Matrix.mul_assoc]`, the same unfold used inline for the length-four case at `TNLean/MPS/MPDO/BNTChannelComposition.lean:87`. It carried no `@[simp]`, had no consumer, and no sibling `physCloseN_two_apply`/`physCloseN_four_apply` exists. |
| `MPOTensor.finOneArrowEquiv` (`TNLean/MPS/MPDO/PhysicalGibbsEmbedding.lean`) | `Equiv.funUnique (Fin 1) (Fin d)` from Mathlib. The removed `private def` rebuilt that equivalence by hand; both use sites now name the Mathlib equivalence directly. It was `private`, so no Blueprint tag or out-of-file consumer named it. |

## Blueprint and documentation redirects

* `def:mpdo_topological_projector_one_fusion`
  (`blueprint/src/chapter/ch21_mpdo_rfp_fusion_isometries_recursive_density.tex`):
  the three `MPOTensor.BNTFusionTensorClause.*` tags were dropped; the entry
  keeps `MPOTensor.BNTFusionCoisometryFamily.projectorQBlock`,
  `.fusionCoisometry_mul_physTraceTransfer_mul_conjTranspose`, and
  `.conjugatedProjectorQBlock`, so `\leanok` remains correct. Its `\uses` no
  longer cites `def:mpdo_bnt_fusion_tensor_clause`, which the entry no longer
  names; that label remains live at its other citation sites.
* `thm:mpdo_topological_projector_one_fusion` (same chapter): the two
  `MPOTensor.BNTFusionTensorClause.*` tags were dropped; the entry keeps
  `MPOTensor.BNTFusionCoisometryFamily.projectorQBlock_eq_unweighted`,
  `.projectorQBlock_isStarProjection`, and
  `.conjugatedProjectorQBlock_isOrthogonalProjection`.
* `thm:mpdo_eta_local_pair_bond_unitary_block_actions`
  (`blueprint/src/chapter/ch21_mpdo_rfp_commuting_form_bond_products.tex`): the
  `EtaLocalStructureData` tag was dropped; the entry keeps
  `MPOTensor.TranslationInvariantBondData.exists_unitary_blockActions_of_pairBond`,
  whose statement is the one the surrounding prose describes.
* `lem:phys_close_three`
  (`blueprint/src/chapter/ch21_mpdo_rfp_renormalization.tex`): the
  `MPOTensor.physCloseN_three_apply` tag was dropped; the entry keeps
  `MPOTensor.physClose3_apply` and
  `MPOTensor.physCloseN_three_eq_physClose3`, which together prove the
  displayed right-associated coefficient formula, so `\leanok` on the
  statement and on the proof remains correct.
* `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`: the sentence naming the
  application of the finite-matrix theorem now cites the
  `TranslationInvariantBondData` form. The eta-local bond is by definition the
  bond of its underlying translation-invariant data, so the sentence and its
  footnote remain true.

## Retained on purpose

* `MPOTensor.BNTFusionIsometryFamily.projectorQBlock` and the four sibling
  declarations of the same names in `TNLean/MPS/MPDO/TopologicalProjectors.lean`
  are independent: they are stated against `fusionIsometry`, not
  `fusionCoisometry`, and carry their own Blueprint role.
* `MPOTensor.EtaLocalStructureData.exists_positive_eta_pairBond_decomposition`
  (`TNLean/MPS/MPDO/CommutingBondEtaDecomposition.lean`) keeps live consumers at
  `TNLean/MPS/MPDO/FixedBondPositivePhysicalSectorConstructor.lean:538` and
  `TNLean/MPS/MPDO/CommutingBondEtaCyclicTransport.lean:66`.
* `MPOTensor.reindex_product_embedLocalOperator_of_etaPair_decomposition`, the
  general cyclic-transport theorem, keeps four consumers.

## Proof-text deduplication in the same change

`TNLean/MPS/MPDO/CompleteZipperFusionSupport.lean` re-derived three fusion-stage
identities inline, twice each. They are now three `private theorem`s in the same
file — `leftIntermediateLetter_eq_sum`,
`leftTripleDirectSumLetter_eq_submatrix`, and
`rightTripleDirectSumLetter_eq_submatrix` — and the six former `have` blocks
each became a one-line application. No public statement changed, so no
Blueprint entry is affected.
