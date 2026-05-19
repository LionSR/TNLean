# CPSV16 non-FT BNT consumer scout

## Scope and bottom line

This memo surveys the remaining non-FT files that mention the old one-copy `IsCanonicalFormBNT` surface and records what a move to the CPSV `IsBNTCanonicalForm` surface would require.

Short summary:

* `TNLean/MPS/RFP/StructuralForm.lean`: trivial port (1-line signature change). It only projects block injectivity.
* `TNLean/MPS/ParentHamiltonian/BiCF/BlockDiagonalCommutant.lean`: moderate for selector/trace-separation lemmas, research-level for statements that pass through assembled tensor projection spans with copy multiplicities.
* `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean`: research-level. The headline theorem is source-true, but the current proof surface is tied to one scalar weight per BNT basis block and cannot survive copy multiplicity by a signature edit.
* `TNLean/PiAlgebra/CanonicalFormSep.lean`: no direct old-BNT theorem; the nearby strict-weight FT lemmas are one-copy FT artifacts and should not be treated as non-FT cleanup.
* `TNLean/PiAlgebra/CanonicalFormSepAux.lean`: no direct old-BNT theorem; it defines old additive interfaces and has doc-only mentions.

## Source anchors used throughout

* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:217-246`: canonical form block weights and the optional global modulus normalization.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:271-301`: BNT definition and the raw two-layer expansion with coefficient `sum_q mu_{j,q}^N`.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:317-344`: injectivity, biCF, and finite blocking to biCF.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:349-361`: proportional and equal MPV theorem statements.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:507-527`: parent Hamiltonian construction and BNT-span ground-space definition.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:1080-1132`: normal-tensor overlap dichotomy, gauge-phase alternative, and eventual LI.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:1148-1192`: BNT matching proof and power-sum multiplicity recovery.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:1274-1307`: RFP normal-tensor form and RFP-to-BNT structural argument.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:1815-1837`: normal tensors after blocking and canonical form.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:1846-1884`: BNT definition and the raw two-layer expansion.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:1890-1906`: proportional/equal FT statements and optional unital gauge.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:1985-2011`: parent Hamiltonian construction from `G_L` and frustration-free ground-state containment.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:2015-2016`: injectivity as span of all matrices for MPS, and normal MPS becomes injective after blocking.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:2041-2094`: injective/normal parent Hamiltonian uniqueness via intersection/regrowing.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:2104-2128`: block-injective canonical form and degenerate ground space spanned by BNT vectors.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:2131-2132`: sector projectors are invisible to the parent Hamiltonian in direct-sum situations.

## New-surface replacement dictionary

| Old fact | Replacement on `IsBNTCanonicalForm P` | Notes |
|---|---|---|
| `hCF.toHasInjectiveBlocks.block_injective j` | `hP.basis_injective j` | Exact replacement for basis-block results. |
| `hCF.toIsLeftCanonicalBlockFamily.leftCanonical j` | `hP.basis_left_canonical j` | Exact replacement; same left-canonical convention. |
| `hCF.toHasNormalizedSelfOverlap.overlap_tendsto_one j` or `hCF.overlap_tendsto_one j` | `hP.basis_normalized_self_overlap j` | Exact replacement; `basis_dim_pos` can avoid some old zero-dimension detours. |
| `hCF.blocks_not_equiv j k ...` | `hP.basis_distinct j k ...` | Exact cast-compatible replacement. |
| external `hIrr.block_irreducible j` | `hP.basis_irreducible j` | New surface often makes the external argument unnecessary. |
| `hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero j` | no direct basis-level scalar; use `P.weight_ne_zero j q` for a selected copy, or `hP.coeff_not_eventually_zero j` for eventual coefficient nonvanishing | This is the main issue. Fixed-length proofs that invert `(mu j)^m` are one-copy artifacts. |
| `hCF.mu_strict_anti` | no core replacement | This strict order is intentionally absent. It belongs only to a separate special subcase if ever needed. |
| `IsCanonicalFormBNT.cross_overlap_tendsto_zero` | `hP.cross_overlap_basis_tendsto_zero` from `SectorBNT/Api.lean` | Exact same BNT-basis conclusion. |
| old LI via `toHasNormalizedSelfOverlap` plus cross decay | `hP.combined_family_eventually_li hQ hAB` or `hP.bnt_data` | Use `bnt_data` for one family; use the API lemma for two families. |
| old `toTensorFromBlocks mu A` | `P.toTensor` with flattened copies, or a grouped theorem stated directly over `P.basis` and `P.coeff` | This is not a drop-in replacement when copies repeat a basis block. |

## `TNLean/MPS/RFP/StructuralForm.lean`

### Top-level old-BNT theorem

| Line | Declaration | One-line statement |
|---:|---|---|
| 260 | `rfp_bnt_structural` | From `IsCanonicalFormBNT mu A`, every block `A k` is injective. |

### Facts actually used

Exhaustive use: `hCF.toIsCanonicalForm.block_injective` at line 264. No use of `mu_strict_anti`, `mu_ne_zero`, `blocks_not_equiv`, cross-overlap decay, left-canonical data, or self-overlap data.

### Paper anchors

This declaration is mostly an interface projection, not a standalone paper theorem. The source support is that the paper BNT consists of normal tensors and, after the relevant blocking, normal tensors become injective or the tensor becomes biCF: CPSV16 lines 271-301 and 317-344; CPSV21 lines 1815-1837 and 2015-2016. The broader RFP structural context is CPSV16 lines 1274-1307.

### Mapping to `IsBNTCanonicalForm`

State the theorem over `P : SectorDecomposition d` and `hP : IsBNTCanonicalForm P` with conclusion `forall j, IsInjective (P.basis j)`, proved by `hP.basis_injective`. No missing replacement.

### Multiplicity preservation check

No reliance on `r_j = 1`. The theorem remains true for arbitrary copy multiplicities because it only speaks about the BNT basis block, not the copy weights.

### Estimated effort

trivial port (1-line signature change).

## `TNLean/MPS/ParentHamiltonian/BiCF/BlockDiagonalCommutant.lean`

### Top-level old-BNT declarations

| Line | Declaration | One-line statement |
|---:|---|---|
| 187 | `wordTupleSpanTop_of_isCanonicalFormBNT_of_blockSelectorWords` | `IsCanonicalFormBNT mu A` plus block selector words gives `WordTupleSpanTop A (1 + S)`. |
| 211 | `wordTupleSpanTop_of_isCanonicalFormBNT_of_pairBlockSeparatingWords` | old BNT plus pair block-separating words gives product-word span at `1 + (r - 1) * S`. |
| 234 | `wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingAt` | old BNT plus fixed-length pair trace separation gives product-word span. |
| 264 | `wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingUpTo_of_identity_padding` | old BNT plus cumulative pair trace separation and identity padding gives product-word span. |
| 293 | `exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairBlockSeparatingWords` | old BNT plus pair block-separating words gives a positive product-word span length. |
| 321 | `exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt` | old BNT plus pair trace separation gives a positive product-word span length. |
| 338 | `forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock` | old BNT plus direct-sum three-block inputs gives pair trace separation at `L + (L + L)`. |
| 354 | `exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock` | existential version of the preceding pair trace separation. |
| 372 | `exists_pos_productWordSpan_of_isCanonicalFormBNT_of_directSum_threeBlock` | old BNT plus three-block inputs gives a positive product-word span length. |
| 396 | `forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_injectiveBlocks` | old BNT plus irreducibility gives uniform pair trace separation at length `6`. |
| 416 | `exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_injectiveBlocks` | existential version of the length-`6` pair trace separation. |
| 428 | `exists_forall_pairSpanTop_period_window_of_isCanonicalFormBNT_of_directSum_injectiveBlocks` | old BNT plus irreducibility gives a pair-span period window. |
| 460 | `exists_pos_productWordSpan_of_isCanonicalFormBNT_of_directSum_injectiveBlocks` | old BNT plus irreducibility gives a positive product-word span length. |
| 524 | `exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_directSum_injectiveBlocks` | word-tuple version of the preceding span result. |
| 550 | `hasBiCF_of_isCanonicalFormBNT_of_directSum_injectiveBlocks` | old BNT plus irreducibility gives `HasBiCF A`. |
| 580 | `pairTraceSeparatingAll_of_isCanonicalFormBNT` | old BNT gives all-words pair trace separation for distinct basis blocks. |
| 605 | `exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_period_windows` | old BNT plus identity period windows gives a common pair trace-separating length. |
| 627 | `exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_identity_period_windows` | old BNT plus identity period windows gives a product-word span length. |
| 649 | `exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_pairSpanTop_period_windows` | old BNT plus pair-span period windows gives a product-word span length. |
| 664 | `exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_directSum_pairSpanTop_period_windows` | direct-sum pair-span windows give product-word span for old BNT blocks. |
| 682 | `exists_pos_productWordSpan_of_isCanonicalFormBNT_of_identity_period_windows` | old BNT plus identity period windows gives a positive product-word span length. |
| 706 | `exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingUpTo_of_identity_padding` | old BNT plus cumulative separation and padding gives positive product span. |
| 747 | `exists_pos_productWordSpan_of_isCanonicalFormBNT_of_blockSelectorWords` | old BNT plus selector words gives a positive product-word span length. |
| 777 | `blockProjection_mem_span_reindexed_toTensorFromBlocks_of_bntSelectorWords` | old BNT plus selector words gives sector-projection membership for `toTensorFromBlocks mu A`. |
| 816 | `isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_bntSelectorWords` | old BNT plus selector words gives the block-diagonal commutant criterion for `toTensorFromBlocks mu A`. |

Sibling old-normal declarations in the same file:

| Line | Declaration | One-line statement |
|---:|---|---|
| 478 | `exists_forall_pairTraceSeparatingAt_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks` | old normal-BNT data plus explicit injectivity gives common pair trace separation. |
| 502 | `exists_pos_productWordSpan_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks` | old normal-BNT data plus explicit injectivity gives positive product-word span. |
| 537 | `exists_wordTupleSpanTop_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks` | word-tuple version of the preceding normal-BNT span result. |
| 564 | `hasBiCF_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks` | old normal-BNT data plus explicit injectivity gives `HasBiCF A`. |

### Facts actually used

Exhaustive old-BNT field use in this file:

* `hCF.toHasInjectiveBlocks` and `.block_injective`: selector-word to span reductions, pair trace separation reductions, fixed-length injectivity at lengths `2` and `6`, all-words pair separation, and selector-to-projection results.
* `hCF.toIsLeftCanonicalBlockFamily`: only in the direct-sum / all-words pair trace separation branch.
* `hCF.toHasNormalizedSelfOverlap`: only in `forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock`.
* `hCF.blocks_not_equiv`: direct-sum / all-words same-dimension separation.
* `hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero`: only in the assembled-tensor projection/commutant selector declarations at lines 787 and 827.
* For `IsNormalCanonicalFormBNT`, the old proof builds an `IsCanonicalFormBNT` using `toIsLeftCanonicalBlockFamily`, `toHasStrictOrderedNonzeroWeights`, `toHasNormalizedSelfOverlap`, and `blocks_not_equiv`, then calls the direct old-BNT theorem; it also uses `toHasIrreducibleBlocks`.

There is no direct use of `mu_strict_anti` for a mathematical estimate in the public conclusions; strict ordering is only carried because the old structure demands it. There is no use of `cross_overlap_tendsto_zero`.

### Paper anchors

The selector/span and biCF declarations correspond to the block-injective canonical form idea: CPSV16 lines 317-344 and CPSV21 lines 2104-2128. Pair trace separation for distinct BNT basis tensors is justified by BNT minimality and the normal-tensor overlap/gauge-phase dichotomy: CPSV16 lines 271-301 and 1080-1132; CPSV21 lines 1846-1861. The projection/commutant declarations are algebraic ingredients toward the parent-Hamiltonian block decomposition whose source statement is CPSV16 lines 507-527 and CPSV21 lines 1985-2011, 2104-2128, and 2131-2132.

### Mapping to `IsBNTCanonicalForm`

For declarations whose conclusion is only about the BNT basis family `A`:

* `toHasInjectiveBlocks` becomes `basis_injective`.
* `toIsLeftCanonicalBlockFamily` becomes `basis_left_canonical`.
* `toHasNormalizedSelfOverlap` becomes `basis_normalized_self_overlap`.
* `blocks_not_equiv` becomes `basis_distinct`.
* external `hIrr` can usually be removed and replaced by `basis_irreducible`.

Clean replacements are missing for the two declarations that pass through `toTensorFromBlocks mu A` using `mu_ne_zero`. On the new surface there is no single `mu j`; the tensor is `P.toTensor`, obtained by flattening copies. For a chosen flattened copy, `P.weight_ne_zero` replaces old scalar nonzero. For a BNT basis sector coefficient, `coeff_not_eventually_zero` only gives eventual nonzero, not nonzero at every fixed word length. Therefore fixed-length inversion of `(mu j)^m` does not port directly.

### Multiplicity preservation check

The pure basis-span and pair-separation declarations do not rely on `r_j = 1`; they talk about distinct BNT basis tensors and should continue to hold for multi-copy BNT.

The assembled projection/commutant declarations do rely on one scalar per basis block. If `P` has two copies over the same basis tensor, `P.flatBasis` repeats that basis block. The fixed-length tuple `s ↦ evalWord (P.flatBasis s) w` cannot span the full product algebra over flattened copies, and `P.coeff m j` may vanish at selected lengths, e.g. weights `(1,-1)`. The likely correct new statement must use grouped sector projections or a multiplicity algebra over each `j`, not the old product algebra over one block per BNT basis element.

### Estimated effort

* Basis-only selector, pair-separation, and `HasBiCF` declarations: moderate (re-state on new surface).
* `blockProjection_mem_span_reindexed_toTensorFromBlocks_of_bntSelectorWords` and `isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_bntSelectorWords`: research-level (genuinely needs the one-copy specialization) unless their conclusions are changed to grouped sector projections for `P.toTensor`.

## `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean`

### Top-level old-BNT declarations

| Line | Declaration | One-line statement |
|---:|---|---|
| 151 | `iSup_chainGroundSpace_block_le_parentHamiltonianGroundSpace` | old BNT gives forward inclusion from the supremum of block chain ground spaces to the assembled parent ground space. |
| 164 | `bnt_mem_groundSpace` | each BNT block MPV is in the assembled parent ground space. |
| 235 | `groundSpaceMap_toTensorFromBlocks_mem_iSup_chainGroundSpace_of_reindexed_projectionSpan` | projection span plus commuting boundary implies the assembled open-chain vector lies in the blockwise ground-space supremum. |
| 343 | `chainGroundSpace_toTensorFromBlocks_le_iSup_of_reindexed_projectionSpan` | boundary representation plus projection span gives reverse block split. |
| 375 | `chainGroundSpace_toTensorFromBlocks_eq_iSup_of_reindexed_projectionSpan` | combines forward and reverse inclusions into equality. |
| 403 | `parentHamiltonianGroundSpace_le_bntSpan_of_block_chain_split` | private endgame: a block split implies parent ground space is contained in `bntSpan`. |
| 442 | `parentHamiltonianGroundSpace_le_bntSpan_of_reindexed_projectionSpan` | projection span plus boundary representation gives containment in `bntSpan`. |
| 474 | `reindexed_projectionSpan_of_wordTupleSpanTop` | private lemma: product-word span gives reindexed projection span for the assembled tensor. |
| 494 | `chainGroundSpace_toTensorFromBlocks_le_iSup_of_wordTupleSpanTop` | product-word span plus boundary representation gives reverse block split. |
| 519 | `chainGroundSpace_toTensorFromBlocks_eq_iSup_of_wordTupleSpanTop` | product-word span plus boundary representation gives equality with blockwise supremum. |
| 544 | `parentHamiltonianGroundSpace_le_bntSpan_of_wordTupleSpanTop` | product-word span plus boundary representation gives containment in `bntSpan`. |
| 570 | `chainGroundSpace_toTensorFromBlocks_le_iSup_of_bntSelectorWords` | old BNT plus selector words plus boundary representation gives reverse block split. |
| 595 | `chainGroundSpace_toTensorFromBlocks_eq_iSup_of_bntSelectorWords` | old BNT plus selector words plus boundary representation gives block split equality. |
| 621 | `parentHamiltonianGroundSpace_le_bntSpan_of_bntSelectorWords` | old BNT plus selector words plus boundary representation gives containment in `bntSpan`. |
| 645 | `parentHamiltonianGroundSpace_le_bntSpan_of_block_decomposition` | unconditional reverse inclusion into `bntSpan` from the intended block decomposition theorem. |
| 691 | `parentHamiltonian_gs_eq_bnt_span` | parent-Hamiltonian ground space equals the span of BNT MPV states. |

### Facts actually used

Exhaustive old-BNT field use in this file:

* `hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero`: forward inclusion through `toTensorFromBlocks`, scalar cancellation in `bnt_mem_groundSpace`, cancellation of `(mu k)^m` in the block-commutation endgame, equality forward inclusion, and projection-span conversion.
* `hCF.toHasInjectiveBlocks.block_injective`: word-span top for a diagonal block and `chainGroundSpace_eq_mpvSubmodule` in the BNT-span endgame.
* `hCF.overlap_tendsto_one`: only to rule out `dim j = 0` in the old surface.
* No direct use of `blocks_not_equiv`, `toIsLeftCanonicalBlockFamily`, `mu_strict_anti`, or cross-overlap decay in this file; those enter only through imported selector/span facts.

### Paper anchors

The forward ground-state inclusion is the direct parent-Hamiltonian construction: CPSV16 lines 511-524 and CPSV21 lines 1985-2011. The reverse inclusion and final equality target the block-injective BNT ground-space theorem: CPSV16 lines 317-344 and 507-527; CPSV21 lines 2104-2128. The scalar block/endgame and invisibility of sector projectors are reflected in CPSV21 lines 2131-2132.

### Mapping to `IsBNTCanonicalForm`

* `toHasInjectiveBlocks.block_injective` becomes `basis_injective`.
* `overlap_tendsto_one` becomes `basis_normalized_self_overlap`; in many places `basis_dim_pos` is a better direct replacement.
* Old `mu_ne_zero` splits into two cases:
  * To embed a single BNT basis MPV into `P.toTensor`, choose a copy `q : Fin (P.copies j)` using `P.copies_pos j` and invert `P.weight j q`.
  * To reason about a grouped basis coefficient, use `P.coeff N j`; only `coeff_not_eventually_zero` is currently available, and it is not enough for fixed finite lengths.

### Multiplicity preservation check

The forward inclusion `bnt_mem_groundSpace` should continue to hold after restatement, because every basis sector has at least one nonzero copy weight. The final theorem is also paper-true in its intended form: CPSV16 and CPSV21 state the ground space is spanned by BNT vectors, not by flattened copies.

The current proof path does not preserve multiplicity. It cancels a fixed scalar `(mu k)^m`, assumes the product-word span separates one virtual block per BNT basis block, and uses projection membership for `toTensorFromBlocks mu A`. With multiple copies, the flattened tensor has repeated basis blocks; full product span over copies is false, and grouped coefficients can vanish at a chosen length. A multi-copy proof needs a statement over grouped BNT sectors or the multiplicity matrix `M_j` in CPSV16 lines 287-301.

### Estimated effort

research-level (genuinely needs the one-copy specialization) for the reverse inclusions and final equality. The forward containment alone is moderate (re-state on new surface), but it is not the migration bottleneck.

## `TNLean/PiAlgebra/CanonicalFormSep.lean`

### Top-level old-BNT declarations

None. The single old-BNT mention is a docstring at line 602 saying the strict ordering witness is available at the old BNT level.

Adjacent strict-weight declarations worth noting:

| Line | Declaration | One-line statement |
|---:|---|---|
| 582 | `per_block_sameMPV_of_separated_canonical_data` | strict nonzero weights plus separated canonical data turn equality of assembled tensors into per-block `SameMPV`. |
| 604 | `per_block_sameMPV_of_canonical_form` | canonical-form version with an explicit strict ordering witness. |
| 632 | `per_block_sameMPV_of_normal_canonical_form` | normal-canonical version with an explicit strict ordering witness. |
| 656 | `fundamentalTheorem_of_separated_canonical_data` | strict separated data gives blockwise gauge equivalence and assembled gauge equivalence. |
| 673 | `fundamentalTheorem_of_separated_canonical_data_explicit` | explicit gauge-matrix version of the preceding theorem. |
| 693 | `fundamentalTheorem_canonicalForm` | canonical-form version with explicit strict ordering witness. |
| 714 | `fundamentalTheorem_canonicalForm_explicit` | explicit gauge-matrix canonical-form version. |

### Facts actually used

No facts are projected from `IsCanonicalFormBNT`. The nearby strict-weight theorems use `HasStrictOrderedNonzeroWeights.mu_strict_anti`, `HasStrictOrderedNonzeroWeights.mu_ne_zero`, `IsCanonicalForm.mu_ne_zero`, `toHasInjectiveBlocks`, `toIsLeftCanonicalBlockFamily`, `toHasNormalizedSelfOverlap`, and the normal-form analogues `block_irreducible`, `leftCanonical`, and `overlap_tendsto_one`.

### Paper anchors

These declarations are old one-copy FT infrastructure. The source theorem and proof are CPSV16 lines 349-361 and 1165-1192, and CPSV21 lines 1890-1906. The source, however, uses BNT multiplicities and power sums at CPSV16 lines 287-301 and 1184-1188, not strict one scalar per BNT basis block.

### Mapping to `IsBNTCanonicalForm`

There is no direct non-FT port. For any future CPSV FT work, replace strict scalar weights by `SectorDecomposition.coeff`, `coeff_not_eventually_zero`, `combined_family_eventually_li`, and Newton-Girard/power-sum recovery. Do not source `mu_strict_anti` from `IsBNTCanonicalForm`, since the new core deliberately omits it.

### Multiplicity preservation check

The strict-weight lemmas rely on `r_j = 1` or an already-collapsed one-copy presentation. They are not valid as stated for arbitrary multi-copy BNT sectors such as weights `(1,-1)` over one basis tensor. Full paper statements need the sector-decomposition FT surface.

### Estimated effort

No non-FT cleanup needed for the old-BNT mention. Any attempt to turn these strict-weight FT lemmas into full multi-copy FT lemmas is research-level, but it belongs with FT migration, not this non-FT consumer cleanup.

## `TNLean/PiAlgebra/CanonicalFormSepAux.lean`

### Top-level old-BNT declarations

None. The old-BNT mentions are doc-only:

* line 230: strict ordering is said to be enforced at the old BNT level.
* line 311: strict ordering is said to be enforced at the old normal-BNT level.

### Facts actually used

No facts are projected from `IsCanonicalFormBNT`. This file defines the old additive interfaces:

* `HasInjectiveBlocks.block_injective`
* `HasIrreducibleBlocks.block_irreducible`
* `HasPrimitiveBlocks.block_primitive`
* `IsLeftCanonicalBlockFamily.leftCanonical`
* `HasOrderedNonzeroWeights.mu_antitone`, `.mu_ne_zero`
* `HasStrictOrderedNonzeroWeights.mu_strict_anti`, `.mu_ne_zero`
* `HasNormalizedSelfOverlap.overlap_tendsto_one`
* `IsCanonicalForm` and `IsNormalCanonicalForm` projections

### Paper anchors

Canonical/normal form anchors are CPSV16 lines 217-246 and CPSV21 lines 1772-1837. BNT multiplicity anchors are CPSV16 lines 271-301 and CPSV21 lines 1846-1884. The strict-order statements in comments are not CPSV for full BNT; they describe the old one-copy surface only.

### Mapping to `IsBNTCanonicalForm`

For non-FT consumers, the new fields replace the structural interfaces: `basis_injective`, `basis_irreducible`, `basis_left_canonical`, `basis_normalized_self_overlap`, `basis_dim_pos`, `basis_distinct`, and `bnt_data`. There is no core replacement for `HasStrictOrderedNonzeroWeights.mu_strict_anti`.

### Multiplicity preservation check

No theorem here depends on `r_j = 1`. The comments tying strict ordering to BNT should eventually be reworded when this file is touched, because strict ordering is not a field of the new BNT core.

### Estimated effort

trivial port (1-line signature change) for the doc-only references, if any cleanup is desired. No theorem migration is needed in this file.

## Cross-file concerns

1. **Fixed-length scalar cancellation is the major blocker.** Old parent-Hamiltonian proofs invert `(mu j)^m`. New sector coefficients are sums of powers and may vanish at specific lengths. `coeff_not_eventually_zero` is insufficient for these fixed-length statements.
2. **Flattened copies are not independent BNT basis blocks.** `P.toTensor` repeats `P.basis j` across copies. Product-span statements over flattened copies generally fail; grouped-sector statements are needed.
3. **Pair separation remains healthy.** Statements about distinct BNT basis tensors should port cleanly via `basis_distinct`, `basis_irreducible`, `basis_left_canonical`, and `cross_overlap_basis_tendsto_zero`.
4. **Normal-sibling old-BNT declarations should be stated directly.** Their current construction of an old canonical-BNT witness only satisfies the old structure, and strict ordering is not used by the target conclusions.

## Recommended migration ordering

Easiest first:

1. `TNLean/MPS/RFP/StructuralForm.lean`: move `rfp_bnt_structural` to `P : SectorDecomposition d` plus `IsBNTCanonicalForm P`.
2. `TNLean/PiAlgebra/CanonicalFormSepAux.lean`: update doc-only strict-order wording if desired.
3. `TNLean/PiAlgebra/CanonicalFormSep.lean`: update the docstring at line 602 only; leave strict FT lemmas for the FT workstream.
4. `TNLean/MPS/ParentHamiltonian/BiCF/BlockDiagonalCommutant.lean`: first port basis-only selector/pair-separation/`HasBiCF` declarations; defer assembled projection/commutant declarations until grouped-sector projection statements are chosen.
5. `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean`: do last. Start with the forward inclusion over `P.toTensor`; treat reverse inclusion and equality as new multi-copy parent-Hamiltonian work rather than a signature edit.
