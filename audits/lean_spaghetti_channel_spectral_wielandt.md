# Lean 4 Spaghetti Audit: Channel / Spectral / Wielandt

Date: 2026-04-08

## Scope and Method

- Scope: every `.lean` file under `TNLean/Channel/`, `TNLean/Spectral/`, and `TNLean/Wielandt/`.
- Files audited: 131.
- `sorry` count below means actual code-level `sorry` after stripping comments/docstrings, not prose mentions such as "sorry-free".
- `simp without only` is reported because you asked for it, even though upstream Mathlib review guidance usually does not treat terminal unsqueezed `simp` as a smell by itself.
- Long-proof metric is a structural heuristic: declaration body spans > 50 lines until the next declaration. It is accurate enough for review triage, but still a heuristic rather than a parsed Lean AST metric.

## Executive Summary

- Actual `sorry`s: 9 total, concentrated in 3 files: TNLean/Channel/FixedPoint/WedderburnDecomp.lean, TNLean/Channel/Schwarz/AndoLieb.lean, TNLean/Channel/Schwarz/OperatorConvexity.lean.
- Direct imports of actual-sorry modules: `TNLean/Channel/Schwarz/OperatorMonotone.lean` imports `OperatorConvexity`; `TNLean/Channel/WolfChapter6Index.lean` imports `FixedPoint.WedderburnDecomp`.
- Worst oversized files: `TNLean/Channel/Peripheral/CyclicDecomposition.lean` (1426 lines); `TNLean/Spectral/SpectralGapNT.lean` (1275 lines); `TNLean/Channel/Determinant.lean` (1202 lines); `TNLean/Spectral/SpectralGap.lean` (1113 lines); `TNLean/Wielandt/RectangularSpan/UniversalityAux.lean` (1097 lines); `TNLean/Channel/Schwarz/PositiveOnAbelian.lean` (1039 lines); `TNLean/Wielandt/Primitivity/StronglyIrreducibleToFullRank.lean` (1035 lines); `TNLean/Channel/Irreducible/Growth.lean` (972 lines).
- Worst proof-size hotspots: `TNLean/Spectral/SpectralGap.lean`:394-978 `eigenvector_gives_gauge` (585 lines); `TNLean/Channel/Peripheral/CyclicDecomposition.lean`:537-1100 `exists_cyclic_projections_of_peripheral_unitary` (564 lines); `TNLean/Spectral/SpectralGapNT.lean`:87-609 `eigenvector_gives_gauge_of_irreducible_TP` (523 lines); `TNLean/Spectral/SpectralGapNT.lean`:751-1203 `dim_eq_of_modulus_one_eigenvector_of_irreducible_TP` (453 lines); `TNLean/Channel/Semigroup/RelaxationConditions.lean`:345-678 `finrank_traceless_blockUT_add_D_le` (334 lines); `TNLean/Channel/Schwarz/PositiveOnAbelian.lean`:458-731 `blockForm_nonneg_of_scalarPSD_of_commuting` (274 lines); `TNLean/Channel/Determinant.lean`:649-917 `heisenberg_dual_multiplicative` (269 lines); `TNLean/Channel/Irreducible/SpectralRadius.lean`:208-471 `spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp` (264 lines).
- Dead documentation artifacts found in code: `TNLean/Wielandt/WielandtBound.lean:264` and `TNLean/Wielandt/RectangularSpan/Universality.lean:836` both end with `: True := trivial` theorems that exist only to anchor prose.
- No immediately closable `sorry`s were found. The remaining ones are either blocked on missing Mathlib infrastructure (`OperatorConvexity`, `AndoLieb`) or on a real algebraic gap (`WedderburnDecomp`).

## High-Severity Findings

- `TNLean/Channel/FixedPoint/WedderburnDecomp.lean` carries 3 actual `sorry`s in the fixed-point Wedderburn story. This is a genuine unsoundness core, not just a cosmetic placeholder.
- `TNLean/Channel/Schwarz/OperatorConvexity.lean` carries 3 actual `sorry`s in Jensen inequalities. `TNLean/Channel/Schwarz/OperatorMonotone.lean` then imports those placeholders, so some proved-looking corollaries are only conditionally sound.
- `TNLean/Channel/Schwarz/AndoLieb.lean` carries 3 actual `sorry`s and is another unsound theorem file in the Chapter 5 pipeline.
- `TNLean/Channel/WolfChapter6Index.lean` is documentation-only, yet it directly imports `FixedPoint.WedderburnDecomp`. That is unnecessary contamination of the import graph.
- `TNLean/Channel/Peripheral/CyclicDecomposition.lean`, `TNLean/Spectral/SpectralGap.lean`, `TNLean/Spectral/SpectralGapNT.lean`, `TNLean/Wielandt/Primitivity/StronglyIrreducibleToFullRank.lean`, and `TNLean/Wielandt/RectangularSpan/UniversalityAux.lean` are all far past the "hard to review / hard to refactor" threshold and should be split along existing section boundaries.

## Copy-Paste / Structural Duplication

- `FixedPoint/StationarySupport.lowerZero_implies_invariance` and `Semigroup/ReducibleQDS/FixedDensity.lowerZero_implies_invariance'` are near-verbatim duplicates of the same support-projection invariance proof skeleton.
- `Irreducible/PerronFrobenius`, `Irreducible/FromSpectral`, and `Irreducible/SpectralRadius` all repeat the same CP-map to Kraus family to irreducible-tensor boilerplate, including the nonzero-Kraus witness extraction.
- `Spectral/SpectralGap`, `Spectral/SpectralGapRect`, and `Spectral/SpectralGapNT` repeat the same gauge-rigidity architecture in square, rectangular, and dimension-mismatch variants instead of factoring a shared core.
- `FixedPoint/Algebra`, `Schwarz/Basic`, and `Schwarz/MultiplicativeDomainFull` each restate small Kraus-map linearity APIs locally. A shared helper module would shrink surface area.

## Redundancy / Mathlib Overlap

- The clearest "already in Mathlib" wrappers are in `TNLean/Channel/Schwarz/OperatorMonotone.lean`: `matrix_rpow_le_rpow` is just a specialization of `CFC.rpow_le_rpow`, and `matrix_log_le_log` is a specialization of `CFC.log_le_log`. They are harmless wrappers, but they are not adding new mathematics.
- I did not find obvious large re-proofs of existing Mathlib theorems beyond those thin wrappers. Most local linearity lemmas are for project-specific maps, so they are duplication inside TNLean more than duplication of Mathlib.

## Closable `sorry`s

- `TNLean/Channel/FixedPoint/WedderburnDecomp.fixedPointAlgebra_wedderburnArtin` is mechanically closable once `fixedPointAlgebra_isSemisimpleRing` exists; the remaining proof should be short because Mathlib already has the Wedderburn-Artin endpoint.
- `TNLean/Channel/FixedPoint/WedderburnDecomp.starSubalgebra_hasWedderburnBlockDecomp` is not immediately closable; it needs a real bridge from abstract Wedderburn-Artin data to the concrete block embedding.
- `TNLean/Channel/Schwarz/OperatorConvexity.*` and all three `TNLean/Channel/Schwarz/AndoLieb.*` placeholders are not locally closable with the current imported API. They depend on missing operator-convexity/Jensen/integration infrastructure, not on a small missed lemma.

## Top `simp` Hotspots

| File | `simp` without `only` |
|---|---:|
| `TNLean/Spectral/SpectralGapNT.lean` | 156 |
| `TNLean/Channel/Peripheral/CyclicDecomposition.lean` | 119 |
| `TNLean/Spectral/SpectralGap.lean` | 71 |
| `TNLean/Channel/Schwarz/PositiveOnAbelian.lean` | 59 |
| `TNLean/Channel/Determinant.lean` | 57 |
| `TNLean/Channel/ChoiJamiolkowski.lean` | 47 |
| `TNLean/Channel/Irreducible/Growth.lean` | 32 |
| `TNLean/Spectral/SpectralGapRect.lean` | 31 |
| `TNLean/Channel/Schwarz/SchwarzSubnormal.lean` | 31 |
| `TNLean/Channel/Semigroup/RelaxationConditions.lean` | 30 |

## Per-File Inventory

| File | Lines | Actual `sorry` | Long proofs >50 | Longest proof | TODO/FIXME/XXX | `simp` no `only` | Notes |
|---|---:|---:|---:|---|---:|---:|---|
| `TNLean/Channel/Basic.lean` | 315 | 0 | 0 | - | 0 | 5 |  |
| `TNLean/Channel/ChoiJamiolkowski.lean` | 650 | 0 | 3 | `cp_iff_choi_posSemidef` 327-410 (84l) | 0 | 47 | split candidate Split candidate: existing sections already separate definition/Kraus API/correspondences/identity-trace; 3 long proofs make this harder to navigate. |
| `TNLean/Channel/DensityRetract.lean` | 278 | 0 | 0 | - | 0 | 9 |  |
| `TNLean/Channel/Determinant.lean` | 1202 | 0 | 6 | `heisenberg_dual_multiplicative` 649-917 (269l) | 0 | 57 | split candidate Highest-priority split in Channel; `heisenberg_dual_multiplicative` alone spans 269 lines. Natural cut: determinant preliminaries, norm<=1 direction, norm=1->unitary direction. |
| `TNLean/Channel/FixedPoint/Algebra.lean` | 491 | 0 | 1 | `krausCommutantStarSubalgebra` 363-422 (60l) | 0 | 22 | Contains another copy of basic Kraus-map linearity lemmas; could share a small common API module with `Schwarz.Basic`/`MultiplicativeDomainFull`. |
| `TNLean/Channel/FixedPoint/CanonicalGauge.lean` | 114 | 0 | 0 | - | 0 | 1 |  |
| `TNLean/Channel/FixedPoint/Cesaro.lean` | 334 | 0 | 3 | `psd_orthogonal_difference_eq_zero` 48-135 (88l) | 0 | 3 |  |
| `TNLean/Channel/FixedPoint/ConditionalExpectation.lean` | 222 | 0 | 0 | - | 0 | 1 |  |
| `TNLean/Channel/FixedPoint/StationarySupport.lean` | 220 | 0 | 0 | - | 3 | 0 | TODOs Contains stale TODOs for Wolf Props. 6.9-6.10. `lowerZero_implies_invariance` is near-duplicate of `ReducibleQDS/FixedDensity.lowerZero_implies_invariance'`. Copy-paste cluster: support-projection invariance proof duplicated in `Semigroup/ReducibleQDS/FixedDensity`. |
| `TNLean/Channel/FixedPoint/WedderburnDecomp.lean` | 246 | 3 | 0 | - | 4 | 0 | actual sorry TODOs 3 actual `sorry`s. `fixedPointAlgebra_wedderburnArtin` is mechanically closable once semisimplicity is proved, but the blocker is substantial (Jacobson-radical/semisimplicity bridge). |
| `TNLean/Channel/Irreducible/Basic.lean` | 169 | 0 | 0 | - | 0 | 9 |  |
| `TNLean/Channel/Irreducible/Ergodicity.lean` | 194 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Irreducible/FromSpectral.lean` | 563 | 0 | 3 | `isIrreducibleMap_of_hasSpectralProperties` 384-553 (170l) | 0 | 26 | split candidate Duplicates the CP->Kraus->irreducible-tensor scaffolding seen in `PerronFrobenius` and `SpectralRadius`; worth extracting a helper. Copy-paste cluster: CP->Kraus->irreducible-tensor setup repeated across the irreducible trilogy. |
| `TNLean/Channel/Irreducible/Growth.lean` | 972 | 0 | 5 | `posDef_of_ker_subset_irreducible_cp` 121-312 (192l) | 0 | 32 | split candidate Large but already sectioned; should be split along existing preservation/one-step/kernel-decrease/growth/orthogonal-trace/exponential boundaries. |
| `TNLean/Channel/Irreducible/PerronFrobenius.lean` | 235 | 0 | 2 | `eigenvalue_unique_of_irreducible_cp` 169-235 (67l) | 0 | 1 | Shares a repeated Kraus-extraction/irreducibility boilerplate block with `FromSpectral` and `SpectralRadius`. Copy-paste cluster: CP->Kraus->irreducible-tensor setup repeated across the irreducible trilogy. |
| `TNLean/Channel/Irreducible/Similarity.lean` | 302 | 0 | 2 | `isIrreducibleMap_similarity` 179-286 (108l) | 0 | 28 |  |
| `TNLean/Channel/Irreducible/SpectralRadius.lean` | 482 | 0 | 2 | `spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp` 208-471 (264l) | 0 | 24 | Shares repeated Kraus-extraction/adjoint-eigenvector setup with `FromSpectral`/`PerronFrobenius`; one 264-line theorem should be broken into helpers. Copy-paste cluster: CP->Kraus->irreducible-tensor setup repeated across the irreducible trilogy. |
| `TNLean/Channel/Irreducible/TraceAdjoint.lean` | 40 | 0 | 0 | - | 0 | 1 |  |
| `TNLean/Channel/KrausFreedom.lean` | 352 | 0 | 1 | `kraus_rectangular_freedom` 159-308 (150l) | 0 | 7 |  |
| `TNLean/Channel/KrausRepresentation.lean` | 203 | 0 | 0 | - | 0 | 7 |  |
| `TNLean/Channel/MaximallyEntangled.lean` | 222 | 0 | 0 | - | 0 | 14 |  |
| `TNLean/Channel/PartialTrace.lean` | 154 | 0 | 0 | - | 0 | 8 |  |
| `TNLean/Channel/Peripheral/ClosureFixedPoint.lean` | 205 | 0 | 2 | `isUnit_peripheral_eigenvector` 52-119 (68l) | 0 | 6 |  |
| `TNLean/Channel/Peripheral/Conjugation.lean` | 59 | 0 | 0 | - | 0 | 2 |  |
| `TNLean/Channel/Peripheral/CyclicDecomposition.lean` | 1426 | 0 | 8 | `exists_cyclic_projections_of_peripheral_unitary` 537-1100 (564l) | 0 | 119 | split candidate Most urgent split candidate in the audit. `exists_cyclic_projections_of_peripheral_unitary` spans 564 lines; file already has clean section boundaries that should become files. |
| `TNLean/Channel/Peripheral/CyclicGroup.lean` | 302 | 0 | 2 | `peripheralEigenvalues_eq_range_primitiveRoot` 172-302 (131l) | 0 | 4 |  |
| `TNLean/Channel/Peripheral/GroupStructure.lean` | 624 | 0 | 5 | `peripheral_eigenvalues_cyclic_structure` 321-452 (132l) | 0 | 13 | split candidate Split cyclic-structure lemmas from multiplicity/closure results. |
| `TNLean/Channel/Peripheral/IrreducibleChannel.lean` | 201 | 0 | 1 | `fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel` 100-152 (53l) | 0 | 8 |  |
| `TNLean/Channel/Peripheral/PeriodicityRemoval.lean` | 116 | 0 | 0 | - | 0 | 4 |  |
| `TNLean/Channel/Peripheral/Powers.lean` | 73 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Peripheral/Spectrum.lean` | 349 | 0 | 1 | `compl_eigenvalue_norm_lt_one_of_primitive` 284-349 (66l) | 0 | 7 |  |
| `TNLean/Channel/PerronFrobenius/Existence.lean` | 389 | 0 | 3 | `exists_posDef_adjoint_eigenvector` 234-317 (84l) | 0 | 9 |  |
| `TNLean/Channel/PerronFrobenius/Normalization.lean` | 319 | 0 | 2 | `exists_supportProjection` 62-154 (93l) | 0 | 23 |  |
| `TNLean/Channel/Primitive.lean` | 169 | 0 | 0 | - | 0 | 9 |  |
| `TNLean/Channel/Schwarz/AndoLieb.lean` | 128 | 3 | 0 | - | 5 | 0 | actual sorry TODOs 3 actual `sorry`s; blocked on missing integration/resolvent infrastructure, so this is not locally closable. |
| `TNLean/Channel/Schwarz/Basic.lean` | 375 | 0 | 2 | `kadison_schwarz` 97-171 (75l) | 0 | 20 | Some duplicated linearity/Kraus-map API overlaps with `FixedPoint.Algebra` and `MultiplicativeDomainFull`. |
| `TNLean/Channel/Schwarz/Douglas.lean` | 75 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Schwarz/KadisonSchwarz.lean` | 243 | 0 | 1 | `kadison_schwarz` 126-185 (60l) | 0 | 3 |  |
| `TNLean/Channel/Schwarz/MultiplicativeDomain.lean` | 261 | 0 | 1 | `ks_gap_eq_sum_squares` 147-197 (51l) | 0 | 2 |  |
| `TNLean/Channel/Schwarz/MultiplicativeDomainFull.lean` | 382 | 0 | 0 | - | 0 | 25 | Repeats basic Kraus-map linearity lemmas already present elsewhere. |
| `TNLean/Channel/Schwarz/MultiplicativeDomainPowers.lean` | 147 | 0 | 0 | - | 0 | 6 |  |
| `TNLean/Channel/Schwarz/OperatorConvexity.lean` | 137 | 3 | 0 | - | 9 | 0 | actual sorry TODOs 3 actual `sorry`s; blocked on Mathlib TODOs plus a missing general Jensen theorem for positive maps. |
| `TNLean/Channel/Schwarz/OperatorMonotone.lean` | 151 | 0 | 0 | - | 0 | 0 | imports actual-sorry module Imports an actual-sorry module. Split the proven wrappers (`matrix_rpow_le_rpow`, `matrix_log_le_log`) into a clean file and quarantine the Jensen-dependent corollaries. |
| `TNLean/Channel/Schwarz/PositiveMapProperties.lean` | 195 | 0 | 0 | - | 0 | 11 |  |
| `TNLean/Channel/Schwarz/PositiveOnAbelian.lean` | 1039 | 0 | 6 | `blockForm_nonneg_of_scalarPSD_of_commuting` 458-731 (274l) | 0 | 59 | split candidate 1k+ lines and one 274-line private lemma. Split diagonal-family machinery from normal-diagonalization/application lemmas. |
| `TNLean/Channel/Schwarz/SchwarzNormal.lean` | 82 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Schwarz/SchwarzNotCP.lean` | 295 | 0 | 0 | - | 0 | 25 |  |
| `TNLean/Channel/Schwarz/SchwarzSubnormal.lean` | 676 | 0 | 4 | `topLeft_schwarz_of_normal_extension` 249-340 (92l) | 0 | 31 | split candidate Split normal-extension setup from commuting-dominant estimates. |
| `TNLean/Channel/Schwarz/TwoPositive.lean` | 363 | 0 | 2 | `kadison_schwarz_2positive` 283-353 (71l) | 1 | 12 | TODOs Has a stale cleanup TODO: reroute `kadison_schwarz_from_2positive` through the 2-positive abstraction instead of delegating back to the direct proof. |
| `TNLean/Channel/Semigroup/Basic.lean` | 617 | 0 | 2 | `continuous_semigroup_hasDerivWithinAt_zero` 319-502 (184l) | 0 | 10 | split candidate Split analytic semigroup preliminaries from the main exponential-semigroup API. |
| `TNLean/Channel/Semigroup/CPClosure.lean` | 344 | 0 | 1 | `IsCPMap.expSemigroup` 286-344 (59l) | 0 | 11 |  |
| `TNLean/Channel/Semigroup/Dissipative.lean` | 236 | 0 | 1 | `expSemigroup_dissipativeDrift_apply` 169-226 (58l) | 0 | 14 |  |
| `TNLean/Channel/Semigroup/GeneratorDefs.lean` | 145 | 0 | 0 | - | 0 | 1 |  |
| `TNLean/Channel/Semigroup/Kernel.lean` | 159 | 0 | 0 | - | 0 | 2 |  |
| `TNLean/Channel/Semigroup/KossakowskiForm.lean` | 273 | 0 | 1 | `kossakowski_iff_lindblad` 196-273 (78l) | 0 | 3 |  |
| `TNLean/Channel/Semigroup/LindbladForm.lean` | 11 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Semigroup/LindbladForm/Basic.lean` | 254 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Semigroup/LindbladForm/ChoiCCP.lean` | 241 | 0 | 1 | `choi_projected_posSemidef_implies_ccp` 59-241 (183l) | 0 | 15 |  |
| `TNLean/Channel/Semigroup/LindbladForm/EulerStep.lean` | 527 | 0 | 2 | `cp_semigroup_implies_ccp_generator` 64-204 (141l) | 0 | 10 | split candidate Over 500 lines; split differentiability/Choi projection lemmas from the final Prop. 7.3 proof. |
| `TNLean/Channel/Semigroup/LindbladForm/GKSLTheorem.lean` | 228 | 0 | 1 | `generator_shift_invariance` 35-89 (55l) | 0 | 1 |  |
| `TNLean/Channel/Semigroup/LindbladForm/TraceBridge.lean` | 204 | 0 | 0 | - | 0 | 3 |  |
| `TNLean/Channel/Semigroup/LindbladForm/Uniqueness.lean` | 271 | 0 | 2 | `generatorDecomp_traceless_unique_kappa_modPhase` 179-256 (78l) | 0 | 7 |  |
| `TNLean/Channel/Semigroup/LiouvillianKernel.lean` | 486 | 0 | 3 | `mem_commutant_of_mem_adjointKernel_of_hasFaithfulStationaryState` 407-474 (68l) | 0 | 12 |  |
| `TNLean/Channel/Semigroup/Perturbation.lean` | 346 | 0 | 2 | `norm_dysonTerm_le` 262-332 (71l) | 0 | 0 |  |
| `TNLean/Channel/Semigroup/Primitivity.lean` | 8 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Semigroup/Primitivity/Basic.lean` | 229 | 0 | 1 | `eq_zero_of_exp_mul_I_isRootOfUnity` 143-216 (74l) | 0 | 4 |  |
| `TNLean/Channel/Semigroup/Primitivity/Helpers.lean` | 410 | 0 | 2 | `peripheral_powers_closed_of_irreducible_channel_with_fixed` 232-370 (139l) | 0 | 10 |  |
| `TNLean/Channel/Semigroup/Primitivity/IrreducibleAnalysis.lean` | 608 | 0 | 0 | - | 0 | 6 | split candidate Split auxiliary spectral/fixed-point lemmas from the main irreducibility analysis. |
| `TNLean/Channel/Semigroup/Primitivity/MainTheorem.lean` | 90 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Semigroup/ProductFormula.lean` | 282 | 0 | 2 | `norm_trotter_pow_sub_exp_le_of_step` 146-201 (56l) | 0 | 4 |  |
| `TNLean/Channel/Semigroup/ReducibleQDS.lean` | 9 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Semigroup/ReducibleQDS/Defs.lean` | 113 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Semigroup/ReducibleQDS/Equivalence.lean` | 125 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Semigroup/ReducibleQDS/FixedDensity.lean` | 195 | 0 | 0 | - | 0 | 0 | Copy-paste cluster: support-projection invariance proof duplicated from `FixedPoint/StationarySupport`. |
| `TNLean/Channel/Semigroup/ReducibleQDS/GeneratorCompression.lean` | 392 | 0 | 4 | `generator_preserves_compression_of_blockUpperTriangular` 211-288 (78l) | 0 | 19 |  |
| `TNLean/Channel/Semigroup/ReducibleQDS/SubsequenceAnalysis.lean` | 389 | 0 | 2 | `generator_vanishes_at_limit` 247-361 (115l) | 0 | 4 |  |
| `TNLean/Channel/Semigroup/RelaxationConditions.lean` | 901 | 0 | 3 | `finrank_traceless_blockUT_add_D_le` 345-678 (334l) | 0 | 30 | split candidate One 334-line theorem dominates the file. Split algebra-generation criteria from kossakowski-rank consequences. |
| `TNLean/Channel/Semigroup/Resolvent.lean` | 42 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/Stinespring.lean` | 200 | 0 | 0 | - | 0 | 3 |  |
| `TNLean/Channel/TensorMap.lean` | 112 | 0 | 0 | - | 0 | 6 |  |
| `TNLean/Channel/TransferMatrix.lean` | 443 | 0 | 0 | - | 0 | 8 |  |
| `TNLean/Channel/WolfChapter2Index.lean` | 111 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Channel/WolfChapter6Index.lean` | 303 | 0 | 0 | - | 1 | 0 | TODOs imports actual-sorry module Documentation-only file that directly imports `FixedPoint.WedderburnDecomp` and therefore pulls actual `sorry`s into the import graph unnecessarily. |
| `TNLean/Channel/WolfChapter6Wrappers.lean` | 69 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Spectral/CrossCorrelation.lean` | 82 | 0 | 0 | - | 0 | 2 |  |
| `TNLean/Spectral/FrobeniusNorm.lean` | 114 | 0 | 0 | - | 0 | 3 |  |
| `TNLean/Spectral/MPVOverlapDecay.lean` | 198 | 0 | 1 | `mpvOverlap_tendsto_zero` 56-112 (57l) | 0 | 4 |  |
| `TNLean/Spectral/MPVOverlapTrace.lean` | 165 | 0 | 2 | `trace_mixedTransferMap_pow_eq_mpvOverlap` 51-109 (59l) | 0 | 2 |  |
| `TNLean/Spectral/MixedTransfer.lean` | 216 | 0 | 0 | - | 0 | 11 |  |
| `TNLean/Spectral/PrimitiveOverlap.lean` | 202 | 0 | 1 | `linearMap_trace_pow_tendsto_one_of_spectralRadius_compl_lt_one` 83-154 (72l) | 0 | 4 |  |
| `TNLean/Spectral/QuantitativeGap.lean` | 438 | 0 | 4 | `correlation_length_bound` 316-414 (99l) | 0 | 12 |  |
| `TNLean/Spectral/SpectralGap.lean` | 1113 | 0 | 2 | `eigenvector_gives_gauge` 394-978 (585l) | 0 | 71 | split candidate Contains a 585-line private lemma (`eigenvector_gives_gauge`). Split HS contraction, gauge rigidity, and convergence into separate files. Copy-paste cluster: same core gauge-rigidity proof pattern is repeated in `SpectralGapRect` and `SpectralGapNT`. |
| `TNLean/Spectral/SpectralGapNT.lean` | 1275 | 0 | 3 | `eigenvector_gives_gauge_of_irreducible_TP` 87-609 (523l) | 0 | 156 | split candidate Very large and heavily duplicated with `SpectralGap`/`SpectralGapRect`; split same-dimension and different-dimension arguments into separate files. Copy-paste cluster: same-/different-dimension gauge proofs mirror `SpectralGap` and `SpectralGapRect`. |
| `TNLean/Spectral/SpectralGapRect.lean` | 612 | 0 | 1 | `dim_eq_of_modulus_one_eigenvector` 297-550 (254l) | 0 | 31 | split candidate Rectangular analogue duplicates large parts of the gauge-rigidity argument from `SpectralGap`/`SpectralGapNT`. Copy-paste cluster: rectangular gauge-rigidity proof largely mirrors `SpectralGap` and `SpectralGapNT`. |
| `TNLean/Spectral/TraceExpansion.lean` | 115 | 0 | 0 | - | 0 | 4 |  |
| `TNLean/Wielandt/FittingDecomposition.lean` | 361 | 0 | 1 | `nilpIndex_le_finrank_maxGenEigenspace_zero` 311-361 (51l) | 0 | 2 |  |
| `TNLean/Wielandt/PaperResults/EigenvectorSpreading.lean` | 67 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Wielandt/PaperResults/MatrixSpanExistence.lean` | 86 | 0 | 0 | - | 0 | 0 | Thin wrapper over backend result; acceptable, but almost all value is in the imported theorem rather than local content. |
| `TNLean/Wielandt/PaperResults/MatrixSpanSharpBound.lean` | 113 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Wielandt/PaperResults/NonzeroTraceWord.lean` | 135 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Wielandt/PaperResults/WielandtInequality.lean` | 350 | 0 | 1 | `iIndex_le_general_of_isPrimitivePaper` 269-350 (82l) | 0 | 3 |  |
| `TNLean/Wielandt/Primitivity/EasyDirections.lean` | 146 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Wielandt/Primitivity/Equivalence.lean` | 282 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Wielandt/Primitivity/ImpliesIrreducible.lean` | 252 | 0 | 1 | `isIrreducibleTensor_of_isPrimitiveMPS_of_posDef` 202-252 (51l) | 0 | 4 |  |
| `TNLean/Wielandt/Primitivity/ImpliesStronglyIrreducible.lean` | 677 | 0 | 3 | `posDef_sum_vecMulVec_of_span_eq_top` 82-162 (81l) | 0 | 10 | split candidate Should split by theorem family; current file mixes positivity preliminaries with the main implication. |
| `TNLean/Wielandt/Primitivity/ImpliesStronglyIrreducibleAux.lean` | 704 | 0 | 2 | `hermitian_pow_fixedPoint_eq_zero_of_trace_eq_zero_of_isPrimitivePaper` 477-558 (82l) | 0 | 7 | split candidate Auxiliary file is large enough to split again; currently mixes trace lemmas and peripheral-primitivity assembly. |
| `TNLean/Wielandt/Primitivity/Normal.lean` | 166 | 0 | 0 | - | 0 | 2 |  |
| `TNLean/Wielandt/Primitivity/PaperDefinitions.lean` | 260 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Wielandt/Primitivity/StronglyIrreducibleToFullRank.lean` | 1035 | 0 | 8 | `hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper` 930-1016 (87l) | 0 | 17 | split candidate Excellent internal sectioning but should be multiple files. Eight named parts already exist and map cleanly to file boundaries. |
| `TNLean/Wielandt/Primitivity/ToNormal.lean` | 225 | 0 | 0 | - | 0 | 5 |  |
| `TNLean/Wielandt/QuantumWielandt.lean` | 100 | 0 | 0 | - | 0 | 0 |  |
| `TNLean/Wielandt/RankOne/BoundedWord.lean` | 538 | 0 | 0 | - | 0 | 19 | split candidate Split bi-rectangular-span API, dimension-growth lemmas, and final bounded-word existence into separate files. |
| `TNLean/Wielandt/RankOne/Construction.lean` | 416 | 0 | 1 | `IsNBlkInjective_transposeTensor` 85-156 (72l) | 0 | 20 |  |
| `TNLean/Wielandt/RankOne/Element.lean` | 230 | 0 | 1 | `range_pow_le_iSup_maxGenEigenspace_ne_zero` 132-194 (63l) | 0 | 13 |  |
| `TNLean/Wielandt/RankOne/Extraction.lean` | 181 | 0 | 1 | `iSup_maxGenEigenspace_ne_zero_le_range_pow` 90-159 (70l) | 0 | 6 |  |
| `TNLean/Wielandt/RankOne/ExtractionFull.lean` | 503 | 0 | 1 | `exists_rankOne_mem_wordSpan_blockTensor` 282-350 (69l) | 0 | 4 | split candidate Sits just over the split threshold; could separate extraction lemmas from final coarse-bound assembly. |
| `TNLean/Wielandt/RankOne/Manufacture.lean` | 57 | 0 | 0 | - | 0 | 4 |  |
| `TNLean/Wielandt/RankOne/Products.lean` | 331 | 0 | 0 | - | 0 | 2 |  |
| `TNLean/Wielandt/RankOne/SpanGrowth.lean` | 137 | 0 | 0 | - | 0 | 3 |  |
| `TNLean/Wielandt/RectangularSpan/Basic.lean` | 380 | 0 | 1 | `wordSpan_le_wordSpan_blockTensor` 119-170 (52l) | 0 | 14 |  |
| `TNLean/Wielandt/RectangularSpan/Growth.lean` | 373 | 0 | 0 | - | 0 | 10 |  |
| `TNLean/Wielandt/RectangularSpan/Ranges.lean` | 324 | 0 | 0 | - | 0 | 21 |  |
| `TNLean/Wielandt/RectangularSpan/Universality.lean` | 838 | 0 | 3 | `vecMulVec_eigenvector_exact_wordSpan` 722-835 (114l) | 0 | 9 | split candidate dead `True := trivial` theorem Contains dead documentation artifact `wielandt_summary_documentation : True := trivial`. Split Section 8g and Section 8h into separate files. |
| `TNLean/Wielandt/RectangularSpan/UniversalityAux.lean` | 1097 | 0 | 2 | `sharp_bound_le` 732-785 (54l) | 0 | 16 | split candidate Another top-priority split candidate; already partitioned into Sections 8c-8f1/2 and should be file-split accordingly. |
| `TNLean/Wielandt/SpanGrowth/CumulativeSpan.lean` | 269 | 0 | 0 | - | 0 | 8 |  |
| `TNLean/Wielandt/SpanGrowth/CumulativeToWordSpan.lean` | 254 | 0 | 0 | - | 0 | 2 |  |
| `TNLean/Wielandt/SpanGrowth/EigenvectorSpreading.lean` | 382 | 0 | 0 | - | 0 | 7 |  |
| `TNLean/Wielandt/SpanGrowth/InvertibleWordSpan.lean` | 533 | 0 | 1 | `wordSpan_eq_top_of_isNormal_of_isUnit` 467-524 (58l) | 0 | 15 | split candidate Over 500 lines; split dimensional preliminaries from the final invertible-word-span theorem. |
| `TNLean/Wielandt/SpanGrowth/NonzeroTraceProduct.lean` | 626 | 0 | 2 | `exists_nonzero_trace_word_sharp_pos` 421-626 (206l) | 0 | 20 | split candidate Over 600 lines; split sharp-normal-span growth from the final nonzero-trace-word extraction. |
| `TNLean/Wielandt/SpanGrowth/VectorToMatrixSpan.lean` | 318 | 0 | 2 | `cumulativeVectorSpan_le_vectorSpreadSpan_of_eigenvector` 142-218 (77l) | 1 | 16 | TODOs Contains a stale TODO note about the remaining hard part of Lemma 2(b). |
| `TNLean/Wielandt/WielandtBound.lean` | 266 | 0 | 1 | `wielandt_chain` 212-263 (52l) | 0 | 0 | dead `True := trivial` theorem Contains dead documentation artifact `wielandt_roadmap : True := trivial`. |

## Recommendation Order

1. Quarantine unsound modules from the default import graph: at minimum `Schwarz/OperatorConvexity`, `Schwarz/AndoLieb`, and `FixedPoint/WedderburnDecomp`, plus their direct documentation/corollary consumers.
2. Split the five worst monoliths first: `Peripheral/CyclicDecomposition`, `Spectral/SpectralGap`, `Spectral/SpectralGapNT`, `Primitivity/StronglyIrreducibleToFullRank`, `RectangularSpan/UniversalityAux`.
3. Extract the repeated helper patterns: support-projection invariance, CP->Kraus->irreducible setup, and gauge-rigidity scaffolding.
4. Delete or move documentation-only `True := trivial` theorems into comments / blueprint text instead of the code namespace.
5. If the team really wants a strict `simp only` policy, start with the hotspot files listed above rather than touching the whole tree at once.

