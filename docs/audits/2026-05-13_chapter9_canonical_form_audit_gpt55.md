**Errata (2026-05-13):** See `audits/2026-05-13_chapter9_FINAL_corrected.md` §3 for the corrected statements. In particular, P18 was wrongly claimed missing in this memo; it is formalized in `TNLean/Algebra/ScalarPowerSumIdentity.lean`.

# Independent audit of Chapter 9: Canonical Form Reduction

Date: 2026-05-13
Auditor: GPT-5.5 parallel second-opinion pass
Scope: `blueprint/src/chapter/ch08_canonical.tex` against
`Papers/1606.00608/MPDO-22-12-17-2.tex` and
`Papers/2011.12127/TN-Review-main.tex`, with Lean declarations under
`TNLean/MPS/CanonicalForm/` and `TNLean/MPS/Structure/`.

I did **not** read any existing audit memo dated 2026-05-13.
I did read the requested style reference in `blueprint/comments202605`.
I did not run `lake build`.

## Executive summary

1. Chapter 9 contains 187 theorem/lemma/proposition/corollary/definition environments by a direct TeX parse.
   The prompt's estimate of about 208 likely counts surrounding remarks or other environments.

2. The paper-side canonical-form core is small: roughly 15--20 statements.
   It consists of invariant-subspace splitting, blocking away periodicity, the definitions of NT/CF/BNT/biCF,
   BNT characterization and decomposition, CFII gauge normalization, Lemma A.1/A.2-style overlap facts,
   the simple power-sum lemma, and the proportional/equal Fundamental Theorem.

3. Chapter 9 is much larger because it contains extensive Lean bookkeeping:
   zero-tail bookkeeping, physical reindexing and cast transport, common-period arithmetic,
   cyclic-sector compression, orbit-sum sector irreducibility, and common blocked cyclic-sector records.
   Much of this is useful implementation infrastructure but is **not** a paper-level theorem.

4. The strongest source-faithfulness problem is convention drift.
   The chapter's `IsNormalCanonicalForm` is a bundled primitive/irreducible/left-canonical/weight-order predicate.
   It is not literally the CF definition in [1606.00608] §2.3 Eq. (II_CF1) or [2011.12127] §IV.A Def. normal/canonical form.
   It also does not by itself encode a BNT in the paper sense.

5. The second strongest issue is loss of the CPSV multiplicity surface.
   The paper's BNT decomposition has sector multiplicities and diagonal matrices `M_j` with coefficients
   `μ_{j,q}`; the formalized normal-CF-BNT and same-structure pathways often enforce strict weight ordering
   or one representative per sector.
   The chapter has some `SectorDecomposition` infrastructure, but the headline NCF/BNT statements do not faithfully state
   [1606.00608] §2.3 Eq. (II_ABasicTensors), Eq. (decBSV), or Appendix A Lemma `Lem:app_simple` recovery.

6. There are several duplicate blueprint rows for the same Lean declaration.
   In particular, `thm:irred_decomp` and `thm:irred_decomp_reduction` both tag
   `MPSTensor.exists_irreducible_blockDecomp`; `thm:sector_decomp_tp_prim_irr` and
   `thm:bnt_sector_decomp_tp_prim_irr_collapsed` both tag
   `MPSTensor.exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`; and
   `thm:ft_after_blocking_structural` and `thm:ft_after_blocking_structural_zero_tail` both tag
   `MPSTensor.afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂`.

7. The chapter largely omits or relocates the actual paper endpoints:
   the exact full CF existence theorem, the BNT iff characterization, the BNT multiplicity formula,
   biCF and `3D^5` block-injectivity, and the proportional/equal FT endpoints.
   Some of these may live in later chapters, but then Chapter 9 should clearly stop presenting its internal shells as
   canonical-form paper statements.

8. My downstream-use classification is based on exact `grep -RInF <lean-name> TNLean blueprint/src` plus a second unqualified-name grep.
   Exact full-name grep undercounts Lean consumers because many uses are unqualified inside namespaces.
   I therefore mark a row `INTERNAL` when unqualified grep shows only the Chapter-9/CanonicalForm pipeline,
   and `USED` when the declaration is visibly consumed in later FT/periodic chapters or non-canonical modules.

---

## Phase 1 -- Paper-side canonical-form targets

The following is the target list I would expect a faithful formalization of the cited canonical-form material to produce.
`Constructive` means the paper gives or sketches an actual construction/reduction; `assertive` means a result is stated as a theorem/lemma/corollary; `definition` is a data surface.

| # | Paper anchor | Statement | Kind |
|---|---|---|---|
| P1 | [1606.00608] §2.3 lines 187--199; [2011.12127] §IV.A lines 1737--1782 | Similarity/gauge transformations leave the MPV family unchanged; upper-triangular off-diagonal blocks do not affect the trace MPV. | constructive observation |
| P2 | [1606.00608] §2.3 Eq. (II_Aiplusk1), lines 201--225; [2011.12127] §IV.A Eq. (II_Aiplusk1), lines 1784--1808 | Iteratively choose minimal invariant subspaces, drop off-diagonal blocks, and obtain `A^i = Σ P_k B^i P_k = ⊕ μ_k A_k^i` with the same MPV family and spectral radii normalized to 1. | constructive |
| P3 | [1606.00608] §2.3 lines 227--231; [2011.12127] §IV.A lines 1815--1820 | Blocking by the lcm of peripheral periods removes nontrivial periodic eigenvalues so each block transfer map becomes primitive. | constructive |
| P4 | [1606.00608] §2.3 Def. NT, lines 233--235 | A normal tensor has no nontrivial invariant projection and its CP map has unique eigenvalue of magnitude/value equal to spectral radius 1. | definition |
| P5 | [2011.12127] §IV.A Def. normal tensor, lines 1827--1830 | A tensor is normal when its transfer operator is a primitive channel; the corresponding MPV is normal. | definition |
| P6 | [1606.00608] §2.3 Def. CF, Eq. (II_CF1), lines 237--244; [2011.12127] §IV.A lines 1831--1837 | Canonical form is a block direct sum `A^i = ⊕ μ_k A_k^i` with each block normal. | definition |
| P7 | [1606.00608] §2.3 Props after construction, lines 249--255; [2011.12127] §IV.A line 1839 | After blocking, any tensor can be replaced by a tensor in CF generating the same MPV family; CF can be characterized by no periodic vectors plus the left/right invariant projection condition. | constructive/assertive |
| P8 | [1606.00608] §2.3 Eq. (II_Psi_k), lines 259--263 | CF directly gives `|V^{(N)}(A)⟩ = Σ_k μ_k^N |V^{(N)}(A_k)⟩`. | assertive formula |
| P9 | [1606.00608] §2.3 Eq. (II:A=XAX), lines 264--268; [2011.12127] §IV.A Eq. (II:A=XAX), lines 1852--1858 | Gauge-phase-equivalent normal blocks represent the same MPV family up to a length-dependent phase. | assertive observation |
| P10 | [1606.00608] §2.3 Def. BNT, lines 271--274; [2011.12127] §IV.A Def. BNT, lines 1846--1850 | A BNT is a set of normal tensors spanning the MPV family at every length and eventually linearly independent. | definition |
| P11 | [1606.00608] §2.3 Prop. `prop:char-BNT`, lines 278--280 and App. A lines 1137--1146; [2011.12127] §IV.A Prop. `prop:char-BNT`, lines 1852--1859 | BNT iff every CF normal block is gauge-phase equivalent to some BNT element and the set is minimal; the proof gives the greedy construction. | constructive iff |
| P12 | [1606.00608] §2.3 Eq. (II_ABasicTensors), Eq. (II_X), Eq. (decBSV), lines 283--302; [2011.12127] §IV.A lines 1864--1884 | Any CF tensor can be written via BNT representatives as `X[⊕_j (M_j ⊗ A_j^i)]X^{-1}`, and the MPV coefficient is `Σ_j(Σ_q μ_{j,q}^N)V(A_j)`. | constructive formula |
| P13 | [1606.00608] §2.3 Def. injective/biCF, lines 317--322; [2011.12127] §IV.A parent-Hamiltonian section lines 2115--2117 | Injective means the physical matrices span the full matrix algebra; biCF means the block diagonal BNT algebra is physically accessible. | definition |
| P14 | [1606.00608] §2.3 Prop. `propblockinj`, lines 340--345; [2011.12127] §IV.A lines 2121--2128 | After blocking at most `3D^5` sites, any CF tensor is in biCF; parent ground spaces are spanned by BNT blocks after suitable length. | constructive/assertive |
| P15 | [1606.00608] App. A CFII, Eq. (II_TPLambda), Eq. (II_XAX), lines 1058--1077; [2011.12127] §IV.A lines 1905--1906 | A CF tensor can be gauged to CFII/left- or unital-canonical orientation with TP/unital normalization and full-rank fixed point; in that gauge FT intertwiners are unitary. | constructive |
| P16 | [1606.00608] App. A Lem. `equalMPS`, lines 1080--1091 | For two NMPVs, self-overlaps tend to 1; cross-overlap modulus tends to 0 or 1; in the 1 case dimensions agree and the tensors are gauge-phase equivalent. | assertive |
| P17 | [1606.00608] App. A Cor. `eqV` and `Lem1`, lines 1121--1133 | Two normal tensors either become orthogonal or are exactly phase-equal for every length; asymptotically orthonormal NMPVs are eventually linearly independent. | assertive |
| P18 | [1606.00608] App. A Lem. `Lem:app_simple`, lines 1155--1163 | Equality of enough power sums of sorted complex lists forces equality of lengths and entries. | assertive |
| P19 | [1606.00608] §2.3 Thm. `thm1`, lines 349--352 and App. A lines 1167--1170; [2011.12127] §IV.A Thm. proportional MPVs, lines 1891--1894 | If two CF tensors generate proportional MPV families for all lengths, their BNT counts agree and BNT blocks match by gauge-phase equivalence. | assertive |
| P20 | [1606.00608] §2.3 Cor. `II_cor2`, lines 354--360 and App. A lines 1172--1192; [2011.12127] §IV.A Cor. equal MPVs, lines 1896--1900 | If two CF tensors generate the same MPV family for all lengths, their total dimensions agree and a single invertible global gauge conjugates one tensor to the other. | assertive |
| P21 | [1606.00608] App. A Cor. `thm:Fundamental-CFII`, lines 1197--1199; [2011.12127] §IV.A lines 1905--1906 | In CFII/unital gauge the gauges in P19/P20 are unitary. | assertive |
| P22 | [2011.12127] §IV.A Thm. `thm:fundamental-general`, lines 1908--1919 | Periodic-block FT without blocking includes an extra diagonal `Z` commuting with the blocks. | assertive |

---

## Phase 2 -- Statement census, coarse grouped pass

Legend:

- `YES` = mathematically nontrivial and useful.
- `TRIVIAL` = true but basically an unfolding/cast/scalar arithmetic wrapper.
- `VACUOUS` = conclusion is mostly a restatement of hypotheses or some hypotheses are unused/inert.
- `INTERNAL` = only supports Chapter-9/CanonicalForm plumbing.
- `USED` = visibly consumed outside this chapter/pipeline, e.g. later FT or non-MPS-channel material.
- `ORPHAN` = no substantive consumer found beyond its own declaration/blueprint row.
- `DUP` = duplicate blueprint statement for an already listed Lean declaration.

| Row | Env / labels | Lean declaration(s) | Paper anchor | Non-vacuous? | Downstream use |
|---:|---|---|---|---|---|
| C1 | definition `def:tensor_from_blocks` | `MPSTensor.toTensorFromBlocks` | P6/P8/P12 support | YES | USED: MPDO vertical CF and many FT/block-sum lemmas |
| C2 | theorem `thm:multi_block_ft` | `MPSTensor.fundamentalTheorem_multiBlock_blocks` | NO_PAPER_ANCHOR: same-index injective special case, not P19/P20 | TRIVIAL | USED: `TNLean/PiAlgebra/FundamentalTheoremComplete.lean` |
| C3 | theorem `thm:block_to_global_mpv` | `MPSTensor.sameMPV_toTensorFromBlocks_of_blockSameMPV` | P8 support only | TRIVIAL | USED: PiAlgebra complete FT wrapper |
| C4 | theorem `thm:multi_block_global` | `MPSTensor.fundamentalTheorem_multiBlock_global` | NO_PAPER_ANCHOR: same-index special case, no BNT/permutation/multiplicity | TRIVIAL | USED: PiAlgebra complete FT wrapper |
| C5 | theorems `thm:injective_smul`, `thm:transfer_smul`, `thm:leftCanonical_phase_scaling`, `thm:mpv_normalize` | `isInjective_smul`; `transferMap_smul`; `leftCanonical_smul_of_norm_one`; `mpv_toTensorFromBlocks_normalize` | P2/P15 support for scaling weights, not independent paper results | TRIVIAL | USED/INTERNAL: `SharedInfra/Scaling.lean`; NCF normalization support |
| C6 | theorem `thm:samempv_unitary` | `MPSTensor.sameMPV_conj_unitary` | P1/P15 | YES | INTERNAL/USED in invariant-subspace and CFII normalization |
| C7 | definitions `def:support_proj`, `def:has_inv_proj` | `MPSTensor.supportProj`; `MPSTensor.HasInvariantProj` | P2/P4 support | YES | USED: channel support/irreducible files; `HasInvariantProj` mostly foundational |
| C8 | theorem `thm:fp_inv_proj` | `MPSTensor.lowerZero_of_posSemidef_fixedPoint` | P2 support; closer to PGVWC/Wolf proof than CPSV statement | YES | USED: Channel fixed-density/stationary-support files |
| C9 | theorem `thm:two_block_decomp` | `MPSTensor.exists_twoBlock_decomp_of_posSemidef_fixedPoint_strict` | P2, but with PSD fixed point and strict support hypothesis | YES | INTERNAL to irreducible decomposition |
| C10 | definition `def:irreducible_tensor` | `MPSTensor.IsIrreducibleTensor` | P4/P5 component | YES | USED widely; exact full-name grep shows channel imports |
| C11 | theorem `thm:irred_decomp` | `MPSTensor.exists_irreducible_blockDecomp` | P2, but unit weights and no spectral-radius weights | YES | INTERNAL/USED by zero-tail and TP-gauge pipeline |
| C12 | theorem `thm:form_II` | `MPSTensor.exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor` | P15, restricted to already TP irreducible block | YES | INTERNAL; exact full name appears mainly in source docstring/blueprint |
| C13 | definitions/theorems `def:alg_span`, `def:invariant_submodule`, `def:irreducible_action`, `thm:irreducible_tensor_to_action`, `thm:burnside_matrix`, `thm:irreducible_action_cumulative_span` | `algSpan`; `IsInvariantSubmodule`; `IsIrreducibleAction`; `isIrreducibleAction_of_isIrreducibleTensor`; `burnside_matrix`; `exists_cumulativeSpan_eq_top_of_isIrreducibleAction` | NO_PAPER_ANCHOR in source A/B; Burnside/Wielandt infrastructure | YES | USED/INTERNAL; belongs better in algebra/Wielandt chapters |
| C14 | theorem `thm:proportional_ft` | `gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one` | P16/P19 close single-block ingredient, not full FT | YES | INTERNAL/USED by BNT/overlap layers |
| C15 | theorems `thm:canonical_from_primitive_fixedpoint`, `thm:canonical_from_primitive` | `isCanonicalForm_of_primitive`; `isCanonicalForm_of_peripheralPrimitive` | NO_PAPER_ANCHOR for source A/B; prepared-data wrapper, cites PGVWC07 not requested source | VACUOUS/TRIVIAL constructor | ORPHAN/weak: first only used by second; second no substantive consumer found |
| C16 | theorems `thm:blocking_primitivity`, `thm:blocking_primitivity_nezero`, `thm:blocking_primitivity_leftcanonical` | `exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor`; `exists_blockTensor_isPrimitive`; `exists_blockTensor_isPrimitive_of_leftCanonical_of_isIrreducibleTensor` | P3/P7 | YES | USED: channel peripheral irreducibility and later blocking |
| C17 | lemmas/theorems `lem:charpoly_conjtranspose`, `thm:eigenvalue_adjoint_conjugate`, `thm:primitive_adjoint_equiv`, `lem:transfer_conjtranspose_adjoint` | corresponding adjoint transport declarations | NO_PAPER_ANCHOR; technical orientation transport for P3/P15 | YES but technical | INTERNAL; `primitive_adjoint_equiv` supports cyclic-sector proofs |
| C18 | definition `def:is_normal_canonical_form` | `MPSTensor.IsNormalCanonicalForm` | MISMATCH with P4/P5/P6: bundled TP+primitive+irreducible+weight order, not paper CF/BNT | YES but restate | USED: Ch11/Ch13 tags; many canonical-form lemmas |
| C19 | theorem `thm:ncf_overlap_tendsto_one` | `IsNormalCanonicalForm.overlap_tendsto_one` | P16 support, derived from primitive blocks | TRIVIAL constructor/projection | INTERNAL/USED by BNT construction |
| C20 | theorem/lemma `thm:nt_modulus_one_gauge`, `lem:overlap_norm_one_implies_spectral_radius_ge_one`, `thm:nt_overlap_norm_one_gauge` | `modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`; `mixedTransferSpectralRadius_ge_one_of_mpvOverlap_norm_tendsto_one`; `gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP` | P16/P17 close | YES | USED in overlap/gauge-phase/BNT layers |
| C21 | theorem `thm:irred_decomp_reduction` | `exists_irreducible_blockDecomp` | P2 | DUP | DUP of C11; delete or merge |
| C22 | theorem `thm:CFII_data` | `exists_CFII_data_of_TP_of_isIrreducibleTensor` | P15, restricted | YES | INTERNAL |
| C23 | theorem `thm:irreducible_block_decomp_with_cfii` | `exists_irreducible_blockDecomp_with_CFII` | P2+P15 but conditional/loose | YES | INTERNAL; exact full-name grep no substantive outside consumer |
| C24 | theorem `thm:exists_normal_canonical_form` | `exists_normalCanonicalForm_of_primitive_blockDecomp` | MISMATCH with P7/P6: assumes prepared primitive distinct-norm block decomposition | VACUOUS-ish wrapper | INTERNAL; only feeds `exists_normalCanonicalForm_of_primitive_input` |
| C25 | definition/theorem `def:zero_mps_tensor`, `thm:mpv_zero_tensor`, `thm:zero_block_separation` | `zeroMPSTensor`; `mpv_zeroMPSTensor`; `exists_irreducible_blockDecomp_nonzeroBlocks` | P2 note `ΣD_k≤D` / zero blocks at [1606.00608] line 219 | YES for bookkeeping; zero tensor itself TRIVIAL | INTERNAL/USED by zero-tail pipeline |
| C26 | theorem `thm:tp_gauge_arbitrary` | `exists_tp_gauge_from_arbitrary_with_zeroTail` | P15+P2, but adds zero-tail convention | YES with convention flag | INTERNAL: input to TP-primitive reduction |
| C27 | theorems `thm:samempv_blocking_distributes`, `thm:samempv_toTensorFromBlocks_block_power`, `thm:block_tensor_to_tensor_from_blocks` | blocking of MPV equality / block sums | P3/P8 support | YES but technical | INTERNAL |
| C28 | definitions/lemmas/theorems `def:flattened_iterated_block_tensor`, `lem:mpv_flattened_iterated_blocking`, `lem:physical_reindex_equiv_transport`, `thm:flattened_iterated_blocking` | reindexing and flattened iterated-blocking declarations | NO_PAPER_ANCHOR; coordinate plumbing | TRIVIAL/technical | INTERNAL; some imported by periodic/common-sector files |
| C29 | theorems `thm:samempv2pos_block_tensor`, `thm:samempv2pos_toTensorFromBlocks_block_power` | positive-length MPV equality after blocking | NO_PAPER_ANCHOR; zero-tail artifact | YES but internal | INTERNAL/USED by Ch11 sector comparison |
| C30 | lemmas `lem:block_weights_ne_zero`, `lem:replicated_weights_pow_ne_zero`, `lem:replicated_weights_pow_mul_phase_ne_zero` | nonzero powers/replicated weights | NO_PAPER_ANCHOR | TRIVIAL | INTERNAL |
| C31 | theorems `thm:primitive_pow`, `thm:primitive_blocking_divisible`, `thm:iterated_blocking_transfer`, `thm:common_blocking_period` | primitive preserved under powers/divisible blocking/common lcm | P3 support | YES | INTERNAL; common-period construction |
| C32 | theorems `thm:iterated_blocking_phys_dim`, `thm:iterated_blocking_samempv_reindex`, `thm:reindex_direct_to_iterated_block_tensor`, `cor:samempv2_reindex_direct_to_iterated_block_tensor`, `thm:samempv_cast_phys_dim`, `thm:tensor_from_blocks_cast_phys_dim`, `thm:left_canonical_cast_phys_dim`, `thm:primitive_transfer_cast_phys_dim`, `thm:irreducible_tensor_cast_phys_dim` | physical dimension and cast transport | NO_PAPER_ANCHOR | TRIVIAL/technical | INTERNAL; relocate |
| C33 | definition/theorems `def:common_period_blocking_ch8`, `thm:common_period_blocking_primitive_ch8`, `thm:common_period_blocking_apply` | `commonPeriodBlocking` and properties | P3 support, but appears again in periodic chapter | TRIVIAL/technical | USED: Ch11b periodic FT tags; duplicate chapter placement |
| C34 | theorem/corollary `thm:compressed_sector`, `cor:compressed_sector_pos_mpv` | `exists_compressedTensor_of_supported_projection`; positive MPV version | NO_DIRECT_PAPER_ANCHOR; compression proof of P3 | YES | INTERNAL |
| C35 | theorems `thm:blockdecomp_commuting_projs`, `thm:blockdecomp_adjoint_fixed` | block decomposition from commuting/adjoint-fixed projections | P3 proof infrastructure, not source theorem | YES | INTERNAL |
| C36 | theorem `thm:conjtranspose_kraus_setup` | `conjTranspose_kraus_setup` | P15/P3 orientation support | YES | INTERNAL |
| C37 | theorems `thm:cyclic_projection_periodic_fixed`, `thm:blocked_adjoint_transfer_pow` | projection cycle and blocked adjoint map | P3 proof plumbing | YES/technical | INTERNAL |
| C38 | theorem `thm:cyclic_sector_decomp_after_blocking` | `exists_cyclic_sector_decomp_after_blocking` | P3, but much more detailed cyclic projection statement | YES | INTERNAL; key period-removal proof |
| C39 | theorem `thm:cyclic_sector_decomp_irr_tp` | `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` | P3/P7 | YES | INTERNAL |
| C40 | theorem/definition `thm:cyclic_sector_decomp_irr_tp_prim_irr`, `def:primitive_irreducible_cyclic_sectors`, `thm:has_primitive_irreducible_cyclic_sectors_tp_irr` | primitive irreducible cyclic sector data | P3/P5 close, but record is Lean-specific | YES | INTERNAL |
| C41 | definitions/theorems `def:common_blocked_cyclic_sector_family`, `def:common_blocked_cyclic_sector_flat_weight`, `def:common_blocked_cyclic_sector_derived_blocks`, `thm:common_blocked_cyclic_sector_derived_properties`, `thm:common_representative_normal_bnt` | `CommonBlockedCyclicSectorFamily` cluster | NO_PAPER_ANCHOR: explicitly internal bookkeeping | YES but internal; flat weight TRIVIAL | INTERNAL; no paper-level row should expose all of this |
| C42 | theorems `thm:common_flat_weight_apply_of_block`, `thm:common_flat_weight_apply_block_eq`, `thm:common_blocked_cyclic_sector_reindexed_samempv`, `def:common_blocked_cyclic_sector_grouped_block_cast`, `thm:common_blocked_cyclic_sector_flatten_word_of_block_cast`, `thm:common_blocked_cyclic_sector_blocked_word_comparison`, `thm:common_blocked_cyclic_sector_reindexed_nonzero_part`, `thm:exists_common_blocked_cyclic_sector_family_common_multiple`, `thm:exists_common_blocked_cyclic_sector_family` | common-sector flatten/reindex/weight suite | NO_PAPER_ANCHOR | TRIVIAL to YES but internal | INTERNAL; strongest relocate candidate |
| C43 | lemmas `lem:pairwise_ortho_proj_sum`, `lem:corner_preserv_adjoint_fixed`, `lem:orbit_sum_fixed`, `lem:orbit_iterate_shifted_sector`, `lem:orbit_iterate_proj`, `lem:orbit_sum_full_sector` | projection/orbit lemmas | NO_PAPER_ANCHOR; Wolf/peripheral proof plumbing | YES but internal | INTERNAL; some exact names used by periodic overlap |
| C44 | theorems/definition `thm:sector_irred_orbit_lift`, `lem:fix_upgrade_peripheral`, `def:sector_fixed_point_algebra_rigidity`, `lem:sector_fixed_algebra_proj_step`, `thm:sector_fixed_algebra_irred_cyclic`, `thm:sector_fixed_algebra_irred_tp`, `thm:sector_fixed_algebra_scalar_blocked` | sector fixed-algebra rigidity | NO_PAPER_ANCHOR | YES but internal | INTERNAL; no source-paper theorem |
| C45 | lemmas/theorems `lem:orbit_sum_hLift_construction`, `lem:orbit_sum_hLift_proj_step`, `lem:orbit_sum_hLift_fixed_algebra`, `thm:orbit_sum_hLift_unconditional`, `thm:sector_irred_fix_upgrade`, `thm:sector_irred_proj_step`, `thm:sector_irred_fixed_algebra`, `thm:sector_irred_unconditional` | orbit-sum sector irreducibility suite | NO_PAPER_ANCHOR | YES but internal | INTERNAL; should be technical appendix |
| C46 | theorems `thm:blocked_sector_proj_step`, `thm:blocked_sector_fixed_algebra`, `thm:blocked_sector_scalar_fixed`, `thm:blocked_sector_unconditional` | primitive/irreducible sector blocks after cyclic decomposition | P3 proof endpoint, not paper-level | YES | INTERNAL |
| C47 | theorem `thm:tp_primitive_blockdecomp` | `exists_tp_primitive_blockDecomp_after_blocking` | MISMATCH with P7: arbitrary tensor to primitive blocks but not full CF/BNT and includes zero tail | YES but restate | INTERNAL/USED by structural after-blocking shells |
| C48 | theorems `thm:normal_tp_primitive_irred`, `thm:tp_primitive_irred_block_injective`, `thm:normal_blocking_preserved` | normality/injectivity from primitive irreducible; blocking preserves normal | P5/P13/P14 support | YES | INTERNAL; `isNormal_blockTensor...` tagged also in Ch7 |
| C49 | theorems `thm:bnt_sorted_reindexing`, `thm:bnt_sorted_blockdecomp`, `thm:bnt_sorted_ncf` | sorting by weight norm and NCF after sorting | NO_PAPER_ANCHOR as theorem; paper allows equal-modulus multiplicities | TRIVIAL/technical | INTERNAL |
| C50 | definition/lemma/theorem `def:trivial_sector_decomp`, `lem:trivial_sector_decomp_same_mpv`, `thm:bnt_trivial_sector` | one-sector-per-block `SectorDecomposition` | P12 support only in special one-copy case | TRIVIAL/technical | INTERNAL |
| C51 | definitions `def:norm_class_grouping_data`, `def:norm_class_grouping` | norm-class enumeration | NO_PAPER_ANCHOR | TRIVIAL/technical | INTERNAL |
| C52 | theorem `thm:unit_modulus_phase_tp_prim_irred` | `norm_gaugePhase_eq_one_of_irr_TP_primitive` | P16/P21 support | YES | INTERNAL |
| C53 | theorem `thm:bnt_grouping_gauge_equiv` | `exists_normClassSectorDecomp_of_equalNorm_sameMPV` | MISMATCH with P10--P12: groups by norm and assumes equal norm => same MPV; not paper BNT | YES but too special | USED: Ch10 BNT tag, but should be flagged |
| C54 | theorem `thm:sector_decomp_tp_prim_irr` | `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` | P10/P11 attempted one-sided BNT construction | YES but not exact BNT iff | DUP of C57 below; INTERNAL |
| C55 | theorem `thm:bnt_li_from_overlap_limits_exists` | `exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal` | P17 | YES | INTERNAL |
| C56 | theorems `thm:bnt_li_tp_prim_irr_separated`, `thm:bnt_sector_decomp_linear_independent`, `thm:bnt_sector_decomp_tp_prim_irr_separated` | separated BNT independence and granular sector construction | P10/P17 support | YES | INTERNAL |
| C57 | definition/theorems `def:mpv_phase_class_data`, `thm:bnt_sector_decomp_tp_prim_irr_collapsed`, `thm:bnt_sector_decomp_tp_prim_irr_collapsed_overlap_ortho`, `thm:bnt_sector_decomp_tp_prim_irr_collapsed_overlap_data`, `thm:bnt_sector_decomp_tp_prim_irr_collapsed_overlap_data_span` | MPV phase classes and one-sided BNT sector construction | P11 close, but relation is MPV-phase and conclusion is `SectorDecomposition`, not paper iff/decomposition | YES but restate | INTERNAL/USED by sector-comparison in Ch11 |
| C58 | theorem `thm:bnt_sector_decomp_tp_prim_irr_linear_independent` | `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_of_linearIndependent` | P10 special case | VACUOUS: TP/primitive/irreducible hypotheses are unused by theorem body | INTERNAL; delete/restate |
| C59 | definitions/lemmas/theorems `def:left_sector_tensor`, `lem:commutes_words`, `lem:left_mul_sector_word`, `lem:left_sector_supported`, `thm:adjoint_fixed_commute_letters` | left-sector tensor and commutation | NO_PAPER_ANCHOR; proof plumbing | YES/TRIVIAL | INTERNAL |
| C60 | theorems `thm:leftcanonical_primitive_blocking`, `thm:normal_from_primitive`, `thm:evalword_zero_allzero`, `thm:mpv_zero_allzero`, `thm:nonzero_kraus_irred`, `thm:allzero_irred_dim_le_one`, `thm:irred_blockdecomp_tpgauge` | existence/zero/nonzero helper suite | P2/P3/P5 support; zero lemmas are internal | MIXED; zero lemmas TRIVIAL | INTERNAL |
| C61 | theorem `thm:blockwise_tp_gauge` | `exists_tp_gauge_blockwise` | P15 restricted blockwise TP gauge | YES | INTERNAL |
| C62 | theorems `thm:normal_live_block_primitive`, `thm:blocked_irreducible_tp_primitive`, `thm:tp_primitive_irreducible_extra_blocking`, `thm:ncf_sorted_tp_primitive_irred`, `thm:ncf_from_primitive_input`, `thm:common_period_two_tensors` | normal/primitive extra-blocking and prepared NCF | P3/P5 support but prepared/technical | MIXED; `ncf_sorted...` constructor | INTERNAL |
| C63 | theorems `thm:ft_after_blocking_structural`, `thm:ft_after_blocking_structural_zero_tail` | both `afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂` | NO_PAPER_ANCHOR as FT; only structural one-sided decompositions, not P19/P20 | YES but misnamed; second DUP | INTERNAL/feeds later Ch11 |
| C64 | theorems `thm:zero_tail_decomp_block_tensor`, `thm:zero_tail_to_tensor_from_blocks_block_power`, `thm:zero_tail_identity_to_tensor_from_blocks_block_power`, `thm:nonzero_block_zero_tail_identity`, `thm:nonzero_block_block_power_zero_tail_identity`, `thm:nonzero_block_same_mpv_zero_tail_eq` | zero-tail transport suite | NO_PAPER_ANCHOR; zero-tail Lean convention | YES but internal | INTERNAL/USED by Ch11 sector comparison |
| C65 | theorems `thm:ft_after_blocking_per_block_cyclic_live_zero_tail`, `thm:ft_after_blocking_common_blocked_cyclic_live_zero_tail`, `thm:ft_after_blocking_reindexed_common_sector_live_zero_tail`, `thm:ft_after_blocking_common_length_common_sector_theorem` | after-blocking cyclic sector data with zero tail | NO_PAPER_ANCHOR as source statement; implementation scaffold for FT | YES but misnamed | INTERNAL/USED by Ch11 sector comparison |
| C66 | theorem groups `thm:zero_tail_common_flat_of_blocked_word_comparison`, `thm:zero_tail_common_flat_of_reindexed`, `thm:samempv_pos_zero_tail_identity_transport`, `thm:zero_tail_common_flat_transport_of_reindexed`, `thm:zero_tail_common_flat_transport_of_grouped_block_cast` | zero-tail/common-sector transport | NO_PAPER_ANCHOR | TECHNICAL | INTERNAL |
| C67 | theorem `thm:after_blocking_common_primitive_irreducible_blocks_reindexed` | `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts` | NO_PAPER_ANCHOR; conditional common-length structural data | YES but conditional | USED by Ch11 `BlockMatchingComparison.lean` |
| C68 | theorem `thm:ft_after_blocking_common_length_common_sector_reindexed` | `afterBlocking_commonLengthCommonSectorData_of_reindexed` | NO_PAPER_ANCHOR; conditional transport | YES but internal | INTERNAL/possibly Ch11 support |

---

## Phase 3 -- Findings

### 3.1 Vacuous / trivial statements

1. `thm:multi_block_ft` / `MPSTensor.fundamentalTheorem_multiBlock_blocks` is just
   `fun k => fundamentalTheorem_singleBlock ...`; it is not the multi-block FT of [1606.00608] `thm1`.

2. `thm:multi_block_global` / `MPSTensor.fundamentalTheorem_multiBlock_global` assumes the block matching in advance
   and only assembles blockwise gauges into a block-diagonal gauge.

3. `thm:block_to_global_mpv` / `MPSTensor.sameMPV_toTensorFromBlocks_of_blockSameMPV` is a direct sum-congruence calculation.
   It is useful, but should not appear as a paper theorem.

4. `thm:injective_smul`, `thm:transfer_smul`, and `thm:leftCanonical_phase_scaling` are elementary scalar arithmetic.
   They should be infrastructure lemmas, not main Chapter-9 statements.

5. `thm:mpv_normalize` is a useful normalization identity, but it formalizes the algebra of moving modulus into the block,
   not a named result of the source papers.

6. The physical-dimension cast row
   (`thm:samempv_cast_phys_dim`, `thm:tensor_from_blocks_cast_phys_dim`,
   `thm:left_canonical_cast_phys_dim`, `thm:primitive_transfer_cast_phys_dim`,
   `thm:irreducible_tensor_cast_phys_dim`) is essentially definitional transport across an equality of naturals.

7. `thm:iterated_blocking_phys_dim` is the arithmetic identity `(d^m)^n = d^(mn)`.
   Keep as code, but relocate out of the paper-level blueprint narrative.

8. `def:common_blocked_cyclic_sector_flat_weight` is the constant-one weight function.
   The chapter itself says the nonzero theorem is trivial; exposing it as a definition row is overkill.

9. `thm:common_flat_weight_apply_block_eq` is a definitional consequence of the transported-weight formula.

10. `thm:ncf_sorted_tp_primitive_irred` is the constructor for `IsNormalCanonicalForm` with the fields supplied as hypotheses.
    This is not a substantive theorem about paper canonical forms.

11. `thm:bnt_sector_decomp_tp_prim_irr_linear_independent` is the clearest genuinely vacuous statement:
    the TP/primitive/irreducible hypotheses are intentionally retained but unused;
    the proof calls `exists_bnt_sectorDecomp_of_linearIndependent μ blocks hμne hLI`.

12. `thm:evalword_zero_allzero` and `thm:mpv_zero_allzero` are necessary zero-tail lemmas but trivial as paper mathematics.

13. `thm:irred_decomp_reduction` duplicates `thm:irred_decomp` exactly at the Lean declaration level.

14. `thm:ft_after_blocking_structural_zero_tail` duplicates `thm:ft_after_blocking_structural` exactly at the Lean declaration level.

15. `thm:sector_decomp_tp_prim_irr` duplicates the Lean declaration later exposed as
    `thm:bnt_sector_decomp_tp_prim_irr_collapsed`.

### 3.2 Orphan internal bookkeeping / strongest deletion or relocation candidates

1. The `CommonBlockedCyclicSectorFamily` block is the biggest internal-bookkeeping island:
   `def:common_blocked_cyclic_sector_family`, `def:common_blocked_cyclic_sector_flat_weight`,
   `def:common_blocked_cyclic_sector_derived_blocks`, `thm:common_blocked_cyclic_sector_derived_properties`,
   `thm:common_representative_normal_bnt`, and the flattening/word-comparison rows through
   `thm:exists_common_blocked_cyclic_sector_family`.
   These have no direct source-paper anchor; they are Lean coordinate management.

2. The sector irreducibility suite
   `lem:orbit_sum_fixed` through `thm:sector_irred_unconditional` is proof infrastructure for the cyclic-sector construction.
   It is not a result stated in CPSV17 §2.3/App. A or TN Review §IV.A.

3. The zero-tail transport suite
   `thm:zero_tail_decomp_block_tensor` through `thm:nonzero_block_same_mpv_zero_tail_eq`, plus
   `thm:zero_tail_common_flat_*`, is a formal response to `N=0` in the Lean MPV definition.
   The paper normally discusses MPVs for physical chains and notes only `ΣD_k≤D`; it does not build a zero-tail theory.

4. The flattened iterated-blocking/reindexing rows are coordinate plumbing.
   They should be in a technical appendix or a Lean-only infrastructure chapter, not in the canonical-form theorem census.

5. The prepared primitive-form rows
   `thm:canonical_from_primitive_fixedpoint`, `thm:canonical_from_primitive`,
   `thm:exists_normal_canonical_form`, and `thm:ncf_from_primitive_input` are conditional constructors.
   They are useful engineering but are not source-paper existence theorems.

6. The norm sorting/norm class rows
   `thm:bnt_sorted_reindexing`, `thm:bnt_sorted_blockdecomp`, `thm:bnt_sorted_ncf`,
   `def:norm_class_grouping_data`, and `def:norm_class_grouping` are pure finite combinatorics.
   The paper does not impose strict norm separation in the BNT formula; it keeps multiplicities.

7. Exact full-name grep found many common-sector declarations only in their own module and the blueprint row.
   Unqualified grep shows internal downstream use, so I do not call them dead code, but they are not paper-level blueprint content.

### 3.3 Mismatched statements

1. `def:is_normal_canonical_form` / `MPSTensor.IsNormalCanonicalForm` is not the paper's CF definition.
   Paper CF is `A^i = ⊕ μ_k A_k^i` with normal blocks [1606.00608] §2.3 Eq. (II_CF1), lines 237--244.
   The Lean predicate is a property of a block family: irreducible, left-canonical, primitive, non-increasing nonzero weights,
   and positive bond dimensions.

2. The chapter conflates or alternates among three notions of normality:
   paper-A NT (`no invariant subspace + unique peripheral eigenvalue`),
   paper-B normal tensor (`primitive channel`), and Lean `IsNormal` (`eventual block injectivity`).
   These are related but not identical as statements.

3. `thm:exists_normal_canonical_form` assumes a primitive irreducible TP block decomposition with pairwise distinct weight norms.
   The source CF existence theorem starts from an arbitrary tensor and constructs the decomposition after blocking.
   Pairwise distinct norms are not a paper hypothesis.

4. `thm:tp_primitive_blockdecomp` produces primitive TP blocks but not directly normal CF in the paper sense because the statement omits tensor irreducibility after blocking.
   Later cyclic-sector rows repair this, but the theorem title overstates the result as a primitive block decomposition endpoint.

5. `thm:bnt_grouping_gauge_equiv` groups by equal weight norm and assumes equal-norm blocks have the same MPV family.
   The paper groups CF normal blocks by gauge-phase equivalence, not by weight norm.
   Equal-norm but inequivalent BNT elements are valid in the paper and should remain separate.

6. `IsCanonicalFormBNT` / `IsNormalCanonicalFormBNT` enforce strict weight-modulus ordering and one representative per strict class.
   The paper's Eq. (II_ABasicTensors) allows multiplicities `r_j` and diagonal matrices `M_j` with several entries `μ_{j,q}`.

7. The structural after-blocking rows labelled as forms of the Fundamental Theorem do not prove the paper FT.
   They produce decompositions of both sides and some positive-length/zero-tail identities.
   They do not conclude `g_a = g_b`, a BNT block permutation, phase factors, gauge matrices, or a global conjugating matrix.

8. The chapter's common reblocking of cyclic sectors is stronger/more detailed than the source blocking argument.
   CPSV17 §2.3 says blocking the lcm of periods removes periodic vectors; it does not construct a reusable common-sector family record.

9. `thm:common_representative_normal_bnt` says representatives form a normal canonical form with BNT separation under extra assumptions.
   This is not Proposition `prop:char-BNT`; it is a later internal construction using a different data structure.

10. The CFII discussion is split across TP-gauge and unitary-diagonal fixed-point steps.
    That split is mathematically reasonable, but the paper statement [1606.00608] App. A lines 1058--1077 is a single gauge-to-CFII statement.
    The chapter should explicitly say its theorems are restricted orientations and intermediate stages.

### 3.4 Missing paper theorems / endpoints

1. Missing as a single theorem: after blocking, any tensor admits a paper CF `A^i = ⊕ μ_k A_k^i` with each `A_k` a normal tensor and same MPV family.
   The pieces are present, but the exact P7 endpoint is not.

2. Missing: the CF characterization proposition [1606.00608] §2.3 lines 253--255:
   no periodic vectors plus every left-invariant projection also right-invariant implies CF.

3. Missing: exact NT definition as a declaration aligned with [1606.00608] §2.3 lines 233--235.
   The chapter has `IsIrreducibleTensor` and primitive transfer-map fields, but not the named paper NT surface.

4. Missing: BNT definition exactly as P10.
   `HasBNTSectorData` captures eventual linear independence for a sector decomposition, but the chapter does not expose the paper BNT definition for a tensor `A`.

5. Missing: Proposition `prop:char-BNT` as an iff with minimality and coverage of all CF normal blocks.
   The phase-class construction is not an iff and does not mention the original CF normal blocks in the paper's way.

6. Missing: Eq. (II_ABasicTensors) with diagonal multiplicity matrices `M_j`, the global block gauge `X`, and the MPV coefficient formula `Σ_q μ_{j,q}^N`.
   `SectorDecomposition` is not a faithful replacement unless explicitly connected to `M_j` and `r_j`.

7. Missing in Chapter 9: injective and biCF definitions from [1606.00608] §2.3 lines 317--322.
   There is `HasBiCF` code in `BlockDiagonalCommutant.lean`, but the chapter does not present the paper definition.

8. Missing in Chapter 9: Proposition `propblockinj`, after at most `3D^5` blocking any CF tensor is biCF.
   Related injectivity-after-blocking facts exist, but not the paper statement.

9. Missing in Chapter 9: Appendix A Lemma `equalMPS` in its full form with overlap dichotomy and gauge-phase conclusion.
   The chapter has split variants, but not the exact lemma.

10. Missing in Chapter 9: Corollaries `eqV` and `Lem1` as paper statements.
    Again pieces exist as overlap/linear-independence facts, but not the source-facing statements.

11. Missing in Chapter 9: Lemma `Lem:app_simple` power-sum recovery.
    It appears in the FundamentalTheorem code/Chapter 11 material, but not in the Chapter-9 canonical-form reduction.

12. Missing in Chapter 9: the proportional FT [1606.00608] `thm1` / [2011.12127] proportional theorem.
    The Chapter-9 structural theorem is not a substitute.

13. Missing in Chapter 9: the equal-MPV corollary [1606.00608] `II_cor2` / [2011.12127] equal theorem.

14. Missing in Chapter 9: CFII unitary corollary [1606.00608] App. A lines 1197--1199 as a paper-facing endpoint.

15. Missing or relocated: [2011.12127] §IV.A periodic general theorem `thm:fundamental-general` lines 1911--1918.
    The chapter points to Chapter 11b, so this may be intentionally out of scope.

### 3.5 Convention drift: paper A vs paper B vs Chapter 9

1. Paper A uses NT/BNT/biCF language.
   Paper B streamlines normal tensor as primitive channel and repeats CF/BNT/FT.
   Chapter 9 uses `IsNormalCanonicalForm`, `IsNormalCanonicalFormBNT`, `SectorDecomposition`, and `HasBNTSectorData`.
   These are not notationally equivalent without bridge theorems.

2. In paper A, BNT multiplicity is central: repeated representatives in the same BNT sector are encoded by `M_j` and weights `μ_{j,q}`.
   Chapter 9 often uses strict weight ordering or one-copy sector decompositions, which hides or removes the multiplicity layer.

3. Paper A's biCF is a physical-index spanning condition over the direct-sum BNT algebra.
   Chapter 9's reduction-to-primitive/injective facts do not state this condition in the paper's form.

4. Paper B's normal tensor definition is primitive channel.
   Chapter 9 sometimes says `normal` for primitive TP irreducible blocks and sometimes refers to Lean `IsNormal`.
   The latter is closer to eventual block injectivity and should not be silently identified with paper-B normality.

5. Orientation differs.
   Paper A App. A CFII uses TP equations `Σ A_k^{i†} A_k^i = I` and a fixed point `E_k(Λ_k)=Λ_k`.
   Paper B §IV.A notes a unital gauge `E_k(I)=I`.
   Chapter 9 correctly discusses left-canonical orientation at the beginning, but many later statements should repeat which side is being used.

6. Period removal in the source is a conceptual blocking step.
   Chapter 9 formalizes it through adjoint cyclic-sector projections and common reblocked sectors.
   This is acceptable proof engineering, but not the same as the paper theorem surface.

---

## Phase 4 -- Recommendations

1. **DELETE** duplicate blueprint row `thm:irred_decomp_reduction` / `MPSTensor.exists_irreducible_blockDecomp`.
   Keep `thm:irred_decomp` as the single row anchored to [1606.00608] §2.3 Eq. (II_Aiplusk1).

2. **DELETE** duplicate blueprint row `thm:ft_after_blocking_structural_zero_tail` /
   `MPSTensor.afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂`.
   Keep one structural row, but rename it so it is not a Fundamental Theorem.

3. **DELETE or MERGE** duplicate row `thm:sector_decomp_tp_prim_irr` with
   `thm:bnt_sector_decomp_tp_prim_irr_collapsed`, both tagging
   `MPSTensor.exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`.

4. **RELOCATE** the physical reindexing/cast suite
   (`lem:physical_reindex_equiv_transport`, `thm:samempv_cast_phys_dim`,
   `thm:tensor_from_blocks_cast_phys_dim`, `thm:left_canonical_cast_phys_dim`,
   `thm:primitive_transfer_cast_phys_dim`, `thm:irreducible_tensor_cast_phys_dim`)
   to a Lean-infrastructure appendix.

5. **RELOCATE** the `CommonBlockedCyclicSectorFamily` definitions and all flattening/word-comparison lemmas
   (`def:common_blocked_cyclic_sector_family` through `thm:exists_common_blocked_cyclic_sector_family`)
   to an internal technical subsection or appendix explicitly marked `NO_PAPER_ANCHOR`.

6. **RELOCATE** the sector irreducibility/orbit-sum suite
   (`lem:orbit_sum_fixed` through `thm:sector_irred_unconditional`) to a proof-infrastructure appendix.
   Cite Wolf/peripheral theory, not CPSV17 §2.3, unless an exact paper statement is added.

7. **RESTATE** `def:is_normal_canonical_form` / `MPSTensor.IsNormalCanonicalForm`.
   Either rename it `PreparedPrimitiveBlockFamily` or add a separate source-faithful `CanonicalForm` definition matching
   [1606.00608] §2.3 Eq. (II_CF1) and [2011.12127] §IV.A lines 1827--1837.

8. **RESTATE** `thm:exists_normal_canonical_form` /
   `MPSTensor.exists_normalCanonicalForm_of_primitive_blockDecomp` as a conditional constructor only.
   Do not cite it as the full CF existence theorem from [1606.00608] §2.3 lines 249--251.

9. **ADD / RESTATE** a paper-facing theorem for P7:
   from arbitrary `A`, after blocking, there exist weights and normal blocks in paper CF, generating the same MPV family.
   Internally this can call zero-tail, TP gauge, period removal, and BNT grouping.

10. **ADD** a source-facing BNT definition and `prop:char-BNT` theorem for P10/P11.
    It should state the iff with coverage of every CF normal block and minimality under gauge-phase equivalence.

11. **ADD** the BNT multiplicity formula P12:
    `A^i = X[⊕_j(M_j ⊗ A_j^i)]X^{-1}` and
    `V(A)=Σ_j(Σ_q μ_{j,q}^N)V(A_j)`.
    This is the main missing bridge between sector data and the paper.

12. **ADD or RELOCATE-IN** biCF material P13/P14:
    the definition of biCF and the `3D^5` block-injectivity proposition.
    If this is already intended for another chapter, Chapter 9 should cross-reference it and not silently skip it.

13. **KEEP-BUT-FLAG** zero-tail statements.
    They are legitimate Lean bookkeeping for length `N=0`, but the memo/prose should say they formalize the paper's
    `ΣD_k≤D` allowance, not an independent CPSV theorem.

14. **RESTATE** `thm:bnt_grouping_gauge_equiv`.
    The current equal-norm hypothesis is too special and not the paper's BNT criterion.
    Rename it `normClassSectorDecomp_of_equalNorm_sameMPV` in prose and stop citing it as Proposition `prop:char-BNT`.

15. **KEEP-BUT-FLAG** the after-blocking structural chain
    (`thm:ft_after_blocking_per_block_cyclic_live_zero_tail` through
    `thm:after_blocking_common_primitive_irreducible_blocks_reindexed`).
    These are useful scaffolding for Chapter 11, but they should be labelled structural scaffolding, not the paper Fundamental Theorem.

---

## Bottom line

Chapter 9 is not mostly wrong mathematically; most Lean statements look true and useful.
The problem is source-facing organization.
Roughly one quarter of the chapter corresponds to recognizable CPSV/TN-Review canonical-form targets.
The rest is internal Lean plumbing, prepared-data constructors, or later FT scaffolding.
The main paper-faithfulness repairs are:

- separate paper CF/NT/BNT/biCF definitions from Lean-prepared primitive block-family predicates;
- restore BNT multiplicities and power-sum recovery as first-class Chapter-9 targets;
- demote common-sector, zero-tail, cast, and reindexing lemmas to infrastructure;
- avoid calling structural decompositions the Fundamental Theorem unless they conclude the paper's gauge-phase/global-gauge endpoints.
