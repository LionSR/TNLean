# One definition per notion of primitivity (2026-11-16)

Issue #10724, the first case of follow-on F4 of
`docs/many_body_circuit_architecture.md`, asked that the nine predicate names
around primitivity be reduced to the three notions they cover, under the rule
"one definition per notion": a source's formulation is honoured by a theorem
whose statement is the source's, not by a predicate per source.

## The notions that remain

| Notion | Definition |
|---|---|
| The peripheral spectrum is `{1}` | `_root_.IsPrimitive`, applied to `Kraus.transferMap A` |
| Some positive word length spans the matrix algebra | `Kraus.IsNormal` |
| Left-canonical, with a fixed point and spectral radius below one on its complement | `Kraus.HasComplementaryFixedPointGap` |

The third notion had a second name, the reducible abbreviation
`MPSTensor.IsPrimitiveMPS`. It was removed in a second change, recorded in the
section "The second name of the third notion" below; the tables before that
section use the names as they are after it.

## Proposition 3 of arXiv:0909.5347

The source introduces three properties of a channel
(`Papers/0909.5347/main.tex:403-430`) and proves them equivalent
(Proposition 3, `:501-509`). The proposition is now the single theorem
`MPSTensor.primitivity_tfae` of `TNLean/Wielandt/Primitivity/Equivalence.lean`:
for `[NeZero D]` and `∑ i, (A i)ᴴ * A i = 1`, a `List.TFAE` of

1. `∃ q, 0 < q ∧ ∀ φ, φ ≠ 0 → Kraus.vectorSpreadSpan A φ q = ⊤`;
2. `∃ n, 0 < n ∧ Kraus.wordSpan A n = ⊤`, which is `Kraus.IsNormal A` by
   definition;
3. `∃ ρ, ρ.PosDef ∧ Kraus.transferMap A ρ = ρ ∧
   (∀ σ, Kraus.transferMap A σ = σ → ∃ c, σ = c • ρ) ∧
   IsPrimitive (Kraus.transferMap A)`.

Clause 3 is the source's literal one. The former predicate
`IsStronglyIrreduciblePaper` added an irreducibility conjunct; irreducibility
is now a conclusion (`MPSTensor.isIrreducibleMap_transferMap_of_isNormal`).

## Removed predicates

| Removed | Replacement |
|---|---|
| `MPSTensor.IsPeripherallyPrimitive A` | `IsPrimitive (Kraus.transferMap A)`, of which it was an abbreviation |
| `MPSTensor.HasPrimitiveFixedPoint A` | `Kraus.HasPrimitiveFixedPoint A`, of which it was an abbreviation |
| `MPSTensor.HasEventuallyFullKrausRank A` | `Kraus.IsNormal A`, to which it was definitionally equal |
| `MPSTensor.IsPrimitivePaper A` | clause 1 of `primitivity_tfae`, written out where a statement is about vector spreading; `Kraus.IsNormal A` where it was a hypothesis |
| `MPSTensor.IsStronglyIrreduciblePaper A` | clause 3 of `primitivity_tfae`; the separate conclusions `IsIrreducibleMap (Kraus.transferMap A)`, `IsPrimitive (Kraus.transferMap A)` and a positive-definite fixed matrix where it was destructured |

## Removed theorems and their replacements

Translations between a removed name and its target are deleted without a
successor; theorems with content are restated on the target.

| Removed | Replacement |
|---|---|
| `hasEventuallyFullKrausRank_iff_isNormal` | none; both sides are `Kraus.IsNormal A` |
| `isStronglyIrreduciblePaper_of` | none (anonymous-constructor forwarder) |
| `isPrimitivePaper_of_hasEventuallyFullKrausRank`, `isPrimitivePaper_of_isNormal` | `exists_vectorSpreadSpan_eq_top_of_isNormal` |
| `isIrreducibleTensor_of_isPrimitivePaper` | `isIrreducibleFamily_of_isNormal`, with `isIrreducibleMap_transferMap_of_isNormal` for the transfer map |
| `isPeripherallyPrimitive_of_isPrimitivePaper` | `isPrimitive_transferMap_of_isNormal` |
| `isStronglyIrreduciblePaper_of_isPrimitivePaper`, `isStronglyIrreduciblePaper_of_hasEventuallyFullKrausRank`, `isNormal_implies_stronglyIrreducible` | `exists_posDef_fixedPoint_of_isNormal`, `isPrimitive_transferMap_of_isNormal`, `isIrreducibleMap_transferMap_of_isNormal` |
| `hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper` | `isNormal_of_isIrreducibleMap_of_isPrimitive` |
| `hasEventuallyFullKrausRank_of_isPrimitiveMPS_of_posDef` | `isNormal_of_hasComplementaryFixedPointGap_with_posDef` |
| `isPrimitiveMPS_of_isStronglyIrreduciblePaper` | `exists_hasComplementaryFixedPointGap_posDef_of_isIrreducibleMap_of_isPrimitive`; from normality, `exists_hasComplementaryFixedPointGap_posDef_of_isNormal` |
| `isStronglyIrreduciblePaper_of_isPrimitiveMPS_of_posDef` | `Kraus.HasComplementaryFixedPointGap.isIrreducibleMap_of_posDef` and `Kraus.HasComplementaryFixedPointGap.isPrimitive`, which were its body |
| `primitivePaper_iff_hasEventuallyFullKrausRank`, `primitivePaper_iff_stronglyIrreducible`, `hasEventuallyFullKrausRank_iff_stronglyIrreducible`, `primitivePaper_iff_exists_simple_peripheral_fixedPoint`, `hasEventuallyFullKrausRank_iff_exists_simple_peripheral_fixedPoint`, `isStronglyIrreduciblePaper_of_simple_peripheral_fixedPoint` | `primitivity_tfae` |
| `hasEventuallyFullKrausRank_of_isPrimitivePaper`, `isNormal_of_isPrimitivePaper` | `((primitivity_tfae A hNorm).out 1 2).mp` |
| `wolf_theorem_6_8_conjunction` | `primitivity_tfae`; its conjuncts were three names of clause 2 and the strengthened clause 3 |
| `isPrimitivePaper_stochasticFamily` | `exists_vectorSpreadSpan_stochasticFamily_eq_top` |
| `CyclicWielandt.isPrimitivePaper` | `exists_vectorSpreadSpan_eq_top_of_isNormal` applied to `CyclicWielandt.isNormal` |
| `qIndex_le_iIndex_of_isPrimitivePaper` | `qIndex_le_iIndex`; for every channel, `qIndex_le_iIndex_of_tracePreserving` |
| `exists_nonzero_trace_word_of_isPrimitivePaper_sharp`, `..._sharp_pos` | `exists_nonzero_trace_word_of_isNormal_sharp`, `..._sharp_pos` |
| `vectorSpreadSpan_eq_top_of_isPrimitivePaper_of_eigenvector` | `vectorSpreadSpan_eq_top_of_isNormal_of_eigenvector` |
| `vecMulVec_mem_wordSpan_of_isPrimitivePaper_of_noninvertible_eigenvector` | `vecMulVec_eigenvector_exact_wordSpan`, of which it was an instance |
| `wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_noninvertible_eigenvector` | `wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_noninvertible_eigenvector` |
| `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector` | `wordSpan_eq_top_of_isNormal_of_noninvertible_eigenvector` |
| `wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_isUnit` | `wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_isUnit` |
| `wordSpan_eq_top_of_isPrimitivePaper_of_isUnit`, `iIndex_le_of_isPrimitivePaper_of_isUnit` | `wordSpan_eq_top_of_isNormal_of_isUnit`, `iIndex_le_of_isNormal_of_isUnit` (already present) |
| `iIndex_le_general_of_isPrimitivePaper` | `iIndex_le_general_of_isNormal` |

All names are in the namespace `MPSTensor` unless qualified.

The following keep their names and change a hypothesis from
`IsPrimitivePaper A` or `HasEventuallyFullKrausRank A` to `Kraus.IsNormal A`:
`qIndex_le_iIndex`, `wolf_theorem_6_15`,
`iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector`,
`iIndex_le_sq_of_noninvertible_eigenvector`,
`iIndex_le_of_mem_wordSpan_one_of_isUnit`. `stochasticFamily_primitive_and_indices`
keeps its name and states its first conjunct as the written-out clause 1.

## Hypotheses of the Wielandt bounds

The source states Lemma 1, Lemma 2 and Theorem 1 for a primitive channel,
that is, for a trace-preserving family satisfying clause 1. The former Lean
statements took the normalization and `IsPrimitivePaper A`, and used the
normalization only to pass to normality through Proposition 3. They now take
`Kraus.IsNormal A`. Where the proof does not use the normalization
(Lemma 1, Lemma 2(b), all three cases of Theorem 1) it is dropped, so those
statements cover the source's hypotheses and more. Lemma 2(a),
`vectorSpreadSpan_eq_top_of_isNormal_of_eigenvector`, keeps the
normalization, which its proof uses.

## Modules

| Module | Change |
|---|---|
| `TNLean/Wielandt/Primitivity/PrimitiveBridge.lean` | deleted; its one surviving theorem is `exists_hasComplementaryFixedPointGap_posDef_of_isIrreducibleMap_of_isPrimitive` in `StronglyIrreducibleToFullRank.lean` |
| `TNLean/Wielandt/Primitivity/PeripheralCriterion.lean` | deleted; its three theorems are clause 3 of `primitivity_tfae` in `Equivalence.lean` |
| `TNLean/Wielandt/Inequality/MatrixSpanSharpBound.lean` | deleted; its one theorem was an instance of `vecMulVec_eigenvector_exact_wordSpan` |

The coherent prerequisite allowlist `scripts/coherent_tn_prerequisites.json`
drops the two deleted modules it named; their content is in the already
listed `TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank` and
`TNLean.Wielandt.RectangularSpan.Universality`. Its recorded baseline commit
is unchanged, so an export needs a new baseline once this change is on `main`.

## Blueprint

In `blueprint/src/chapter/ch08_wielandt_cumulative_bound.tex` the three
definition entries for the source's properties are replaced by a paragraph of
prose, the equivalence entries are merged into the one entry
`thm:wielandt_proposition_three`, and the entries for Lemma 1, Lemma 2 and
Theorem 1 are stated for a normal tensor. Removed labels and where their
dependencies now point:

| Removed label | Redirected to |
|---|---|
| `def:eventually_full_kraus_rank` | `def:normal` |
| `def:paper_primitive`, `def:strongly_irreducible_paper` | the statement using the property; `thm:wielandt_proposition_three` |
| `thm:wolf_6_8_kraus_span`, `thm:wolf_6_8_conjunction`, `rem:wolf_6_8_pairwise`, `thm:wielandt_literal_peripheral_criterion` | `thm:wielandt_proposition_three` |
| `thm:strongly_irreducible_of_paper_primitive` | `thm:normalized_normal_strongly_irreducible` |
| `thm:rank_one_noninvertible_eigenvector_primitive` | `lem:rank_one_noninvertible_eigenvector` |
| `cor:wielandt_case2_generator` | `thm:wielandt_case2_normal_generator` |

## The second name of the third notion

Decision of 2026-11-16 on issue #10724: `Kraus.HasComplementaryFixedPointGap`
is the one name; the abbreviation `MPSTensor.IsPrimitiveMPS` is deleted with
no deprecated alias. The definition is QICLean's, and a notion has no second
name in a downstream namespace. The predicate takes the fixed point `ρ` and
contains the trace-preserving normalization, neither of which the words
"primitive matrix product state" say. The change is confined to TNLean.

Every statement that named `IsPrimitiveMPS A ρ` now names
`Kraus.HasComplementaryFixedPointGap A ρ`; no statement changes otherwise.

### Lemmas of the former namespace

The 77 declarations `MPSTensor.IsPrimitiveMPS.x` are now
`Kraus.HasComplementaryFixedPointGap.x`, with `x` unchanged, so that
`hP.x` still resolves on `hP : Kraus.HasComplementaryFixedPointGap A ρ`:

`blockTensor`, `bulkObservable_cross_groundSpace_compression_tendsto_zero_of_inequivalent`, `bulkObservable_groundSpace_compression_tendsto_scalar`, `bulkObservable_groundSpace_compression_tendsto_zero`, `bulkObservable_groundSpace_projection_eventually_near_expectation`, `bulkObservable_groundSpace_projection_norm_sq_tendsto_zero`, `bulkObservable_groundState_expectation_tendsto`, `bulkObservable_groundState_norm_sq_tendsto`, `c3_centeredVirtualResidualES_norm_sq_le_geometric`, `commutator_gap_of_bulkObservable_energy_limit`, `eq_quasiLocalExpectation_of_groundSpace_support`, `eventually_fnwMixingQuantity_le_of_pos_prefactor`, `eventually_groundSpaceGram_isUnit_and_inverse_bound`, `eventually_groundSpaceMapES_injective_and_inverseGram_bound`, `eventually_norm_inner_blockedResidualBoundaryMapES_le_of_inequivalent`, `eventually_norm_inner_groundSpaceES_le_of_inequivalent`, `eventually_norm_inner_groundSpaceES_le_of_mixed_gap`, `eventually_norm_residualWindow_cross_projection_le_of_inequivalent`, `eventually_openChain_groundProjection_defect_mul_sqrt_lt`, `eventually_parentHamiltonianES_gap_ge_one_sub`, `eventually_projector_defect_le_of_pos_prefactor`, `eventually_residualBoundaryGramInverse_properties`, `eventually_wholeIncrement_groundProjection_defect_le`, `exists_blockTensor_anticommutator`, `exists_blockTensor_parentHamiltonianES_gap_eighth`, `exists_blockTensor_parentHamiltonianES_gapped`, `exists_eventually_unit_groundSpaceES`, `exists_fixedAmbient_martingaleDifference_norm_lt_c3_threshold`, `exists_fnwMixingQuantity_le_geometric`, `exists_fnwMixingQuantity_le_geometric_of_transfer_eigenvalues`, `exists_openChain_groundProjection_defect_le_fnw_geometric`, `exists_openChain_groundProjection_defect_lt_c3_threshold`, `exists_openChain_martingaleDifference_norm_lt_c3_threshold`, `exists_openParentHamiltonianES_gap`, `exists_parentHamiltonianES_gap_of_finiteRangeKnabe`, `exists_pos_localCommutator_gap_of_isParentInteraction`, `exists_pos_localCommutator_gap_of_wielandt_range`, `exists_pos_quasiLocalCommutator_gap_of_isParentInteraction`, `exists_re_inner_openChain_anticommutator_ge_c3_threshold`, `exists_threeBlock_wholeIncrement_defect_le_seven_sixteenths`, `exists_uniform_wholeIncrement_defect_le_seven_sixteenths`, `exists_wholeIncrement_groundProjection_defect_le_fnw`, `exists_wholeIncrement_groundProjection_defect_le_fnw_geometric`, `fnwLowerBoundaryConstant_mono`, `fnwRemainder_eigenvalue_norm_lt_one`, `fnwTransferMap_sub_fnwLimitMap_pow`, `fnwTransfer_hasEigenvalue_of_remainder`, `fnwWeightedRemainderSpectralRadius_lt_of_transfer_eigenvalues`, `fnwWeightedRemainder_spectralRadius_lt_one`, `groundSpaceES_starProjection_comp_tendsto_zero_of_inequivalent`, `groundSpaceGram_geometric_inverse_bounds`, `groundSpaceGram_ringInverse_tendsto`, `groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric`, `groundSpaceGram_tendsto_gramReshuffle_fixedPointProj`, `groundSpaceMapES_bulkObservable_compression_tendsto`, `groundSpaceMapES_geometric_inverseGram_bounds`, `isPureQuasiLocalState_quasiLocalExpectation`, `localCommutatorObservable_expectation_tendsto`, `localCommutator_gap_of_openInteraction_gap`, `localCommutator_gap_of_open_gap`, `observableInsertionExpectation_nonneg`, `observableInsertionExpectation_one`, `openInteraction_commutator_energy_tendsto`, `overlap_tendsto_one`, `physicalObservableTransfer_sandwich_tendsto`, `quasiLocalState_interval_eq_insertion_of_groundSpace_support`, `reindexPhysical`, `residualBoundaryGramInverse_sub_limit_tendsto_zero`, `residualBoundaryGram_sub_limit_norm_sq_le_geometric`, `residualWindowMixedGramResidual_tendsto_zero`, `residualWindow_cross_projection_tendsto_zero_of_inequivalent`, `residualWindow_projection_comp_sub_tendsto_zero`, `smul_inv_trace`, `tailVirtualMapES_norm_four_pow_uniform`, `tailVirtualMapES_norm_uniform`, `transferMap_pow_tendsto_fixedPointProj`, `wholeIncrementCenteredResidualES_norm_le`.

Four of them concern the predicate and Kraus-level operations only, and are
candidates to move to QICLean: `smul_inv_trace` (with its three auxiliary
lemmas `fixedPointProj_smul`, `Matrix.trace_inv_trace_smul` and
`Matrix.PosDef.inv_trace_smul` of
`TNLean/MPS/Structure/PrimitiveFixedPoint.lean`),
`transferMap_pow_tendsto_fixedPointProj`, `reindexPhysical` and `blockTensor`.
The proof of `blockTensor` uses
`MPSTensor.tp_primitive_irreducible_extra_blocking`, which would have to move
with it. The others involve ground spaces, parent Hamiltonians, overlaps or
the transfer conventions of the gap proofs, and stay in TNLean.

### Renamed theorems

All in the namespace `MPSTensor`.

| Old name | New name |
|---|---|
| `IsPeriodic.exists_isPrimitiveMPS_groundSpaceDecomposition` | `IsPeriodic.exists_hasComplementaryFixedPointGap_groundSpaceDecomposition` |
| `IsPeriodic.exists_isPrimitiveMPS_groundSpaceDecomposition_of_dvd` | `IsPeriodic.exists_hasComplementaryFixedPointGap_groundSpaceDecomposition_of_dvd` |
| `eventually_iSup_groundSpace_restriction_intersection_of_isPrimitiveMPS` | `eventually_iSup_groundSpace_restriction_intersection_of_hasComplementaryFixedPointGap` |
| `exists_eventually_wordTupleSpanTop_of_isPrimitiveMPS` | `exists_eventually_wordTupleSpanTop_of_hasComplementaryFixedPointGap` |
| `exists_ge_openParentHamiltonianES_toTensorFromBlocks_gap_all_of_isPrimitiveMPS` | `exists_ge_openParentHamiltonianES_toTensorFromBlocks_gap_all_of_hasComplementaryFixedPointGap` |
| `exists_ge_openParentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS` | `exists_ge_openParentHamiltonianES_toTensorFromBlocks_gap_of_hasComplementaryFixedPointGap` |
| `exists_ge_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS` | `exists_ge_parentHamiltonianES_toTensorFromBlocks_gap_of_hasComplementaryFixedPointGap` |
| `exists_isPrimitiveMPS_family_of_isNormal` | `exists_hasComplementaryFixedPointGap_family_of_isNormal` |
| `exists_isPrimitiveMPS_family_of_wordTupleSpanTop` | `exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop` |
| `exists_isPrimitiveMPS_family_parentHamiltonianES_eq_of_common_isNBlkInjective` | `exists_hasComplementaryFixedPointGap_family_parentHamiltonianES_eq_of_common_isNBlkInjective` |
| `exists_isPrimitiveMPS_family_parentHamiltonianES_eq_of_isNormal` | `exists_hasComplementaryFixedPointGap_family_parentHamiltonianES_eq_of_isNormal` |
| `exists_isPrimitiveMPS_family_parentHamiltonian_eq_of_wordTupleSpanTop` | `exists_hasComplementaryFixedPointGap_family_parentHamiltonian_eq_of_wordTupleSpanTop` |
| `exists_isPrimitiveMPS_gauge_of_isNormal` | `exists_hasComplementaryFixedPointGap_gauge_of_isNormal` |
| `exists_isPrimitiveMPS_of_isPeriodic_one` | `exists_hasComplementaryFixedPointGap_of_isPeriodic_one` |
| `exists_isPrimitiveMPS_posDef_of_isIrreducibleMap_of_isPrimitive` | `exists_hasComplementaryFixedPointGap_posDef_of_isIrreducibleMap_of_isPrimitive` |
| `exists_isPrimitiveMPS_posDef_of_isNormal` | `exists_hasComplementaryFixedPointGap_posDef_of_isNormal` |
| `exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_isPrimitiveMPS` | `exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_hasComplementaryFixedPointGap` |
| `exists_nonzero_evalWord_of_isPrimitiveMPS` | `exists_nonzero_evalWord_of_hasComplementaryFixedPointGap` |
| `exists_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS` | `exists_parentHamiltonianES_toTensorFromBlocks_gap_of_hasComplementaryFixedPointGap` |
| `exists_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS_of_threeBlock_bound` | `exists_parentHamiltonianES_toTensorFromBlocks_gap_of_hasComplementaryFixedPointGap_of_threeBlock_bound` |
| `exists_parentHamiltonianES_toTensorFromBlocks_gap_threshold_of_isPrimitiveMPS` | `exists_parentHamiltonianES_toTensorFromBlocks_gap_threshold_of_hasComplementaryFixedPointGap` |
| `exists_positive_parent_interaction_groundStateFace_of_isPrimitiveMPS` | `exists_positive_parent_interaction_groundStateFace_of_hasComplementaryFixedPointGap` |
| `exists_positive_parent_interaction_of_isPrimitiveMPS` | `exists_positive_parent_interaction_of_hasComplementaryFixedPointGap` |
| `exists_uniform_blockGroundSpaceMapES_injective_of_compact_isPrimitiveMPS` | `exists_uniform_blockGroundSpaceMapES_injective_of_compact_hasComplementaryFixedPointGap` |
| `groundSpace_supported_iff_convex_combination_of_isPrimitiveMPS` | `groundSpace_supported_iff_convex_combination_of_hasComplementaryFixedPointGap` |
| `isNormal_of_isPrimitiveMPS_with_posDef` | `isNormal_of_hasComplementaryFixedPointGap_with_posDef` |
| `isPure_groundSpace_supported_iff_sector_of_isPrimitiveMPS` | `isPure_groundSpace_supported_iff_sector_of_hasComplementaryFixedPointGap` |
| `markovTensor_isPrimitiveMPS` | `markovTensor_hasComplementaryFixedPointGap` |
| `transferMap_pow_ne_zero_of_isPrimitiveMPS` | `transferMap_pow_ne_zero_of_hasComplementaryFixedPointGap` |

### Removed theorem

`MPSTensor.isIrreducibleTensor_of_isPrimitiveMPS_of_posDef` had the statement
and the proof of QICLean's
`Kraus.HasComplementaryFixedPointGap.isIrreducibleFamily_of_posDef`. It is
deleted; it had no caller, and the blueprint entry
`lem:primitive_implies_irreducible` now points to the QICLean theorem.

### Not changed

`Kraus.HasPrimitiveFixedPoint`, the existential over `ρ`, is defined in
QICLean. TNLean uses it in two places and destructures it at once in both.
Removing it is a QICLean change and is left for one.
