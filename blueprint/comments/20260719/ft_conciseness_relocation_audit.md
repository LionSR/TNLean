# FT--MPS conciseness and relocation audit

Date: 2026-07-19

## Scope and method

This began as a read-only audit of `blueprint/src/content_ft_mps.tex`, which
then consisted exactly of Chapters 1--12. The full router `blueprint/src/content.tex`
continues to place Chapter 12 immediately after the Chapter 11 Fundamental-Theorem
proof.

A **safe relocation candidate** is a whole section, subsection, or genuinely
self-contained consecutive cluster that supplies no Chapter 11 prerequisite,
and whose removal does not impair the remaining exposition. **Essential** means
it is on the current route to Chapter 11. **Supporting/retain-for-flow** means
that it is technically avoidable at the current abstraction boundary but should
remain to preserve a readable Wolf-derived narrative. **Uncertain** means do
not move it in this conservative pass.

The Lean dependency direction supports treating symmetry as post-theorem
material. `TNLean/MPS/Periodic/FundamentalTheorem.lean` imports MPS
definitions, overlap, Z-gauge, and scalar-power-sum infrastructure; it does
not import `TNLean/MPS/Periodic/Symmetry.lean`. Conversely, the latter imports
modules with an equal-case Fundamental-Theorem hypothesis. The recent channel
fixed-point documentation commits `fdeb32b7`, `0f100e92`, and `4493a08c` also
make clear that the stationary-support and fixed-point-algebra material should
be moved only as a coherent cluster, never deleted or casually split.

`blueprint/README.md` and the historically named
`scripts/build_blueprint_ch01_12.sh` now define and check the focused
Chapters 1--11 route.  The full router retains Chapter 12 immediately after
the proof.

## Retained proof spine

\[
\text{MPS data/gauges}
\to \text{injectivity, normality, blocking}
\to \text{channel PF and Schwarz input}
\to \text{mixed-transfer separation}
\to \text{Wielandt fixed-length injectivity}
\to \text{canonical reduction}
\to \text{BNT matching and copy weights}
\to \text{Chapter 11}.
\]

The principal anchors are:

- Chapter 2: `def:mps_tensor`, `def:same_mpv2_pos`,
  `def:gauge_phase_equiv`, `def:normal`, `def:blocked_tensor`.
- Chapter 3: `thm:ft_single`, `thm:simplicity`, `thm:skolem_noether`.
- Chapter 4: `def:irreducible_cp`, `thm:transfer_channel`,
  `thm:peripheral_roots_irred_fp`, `def:primitive_channel`.
- Chapter 5: `thm:kadison_schwarz`, `thm:kraus_commute`,
  `thm:ks_peripheral`, `thm:left_multiplicative_identity`.
- Chapter 6: `thm:psd_fp_pd_irred`, `thm:qpf`,
  `thm:right_canonical_gauge`, `thm:left_canonical_gauge`.
- Chapter 7: `thm:overlap_decay`, `thm:overlap_decay_rect`,
  `thm:modulus_one_gauge_irr_tp`, and the irreducible TP variants.
- Chapter 8: `thm:wielandt_lemma2b`,
  `thm:normal_from_primitive_posdef`,
  `thm:tp_primitive_irred_block_injective`.
- Chapter 9: common blocking, cyclic-sector, and primitive-block reduction.
- Chapter 10: `def:sector_bnt_cf`,
  `lem:eventual_coeff_eq_of_eventual_li`,
  `thm:sector_bnt_bijective_match_of_sameMPV`, and
  `lem:sector_bnt_matched_sector_weight_equiv`.
- Chapter 11: `thm:sector_bnt_proportional_global_gauge_of_coeff_identity`
  and `thm:sector_bnt_equal_mps_gaugeEquiv_literal`.

In particular, Chapter 11 explicitly uses the Chapter 10 matching and
copy-weight labels and Chapter 9's
`thm:ft_after_blocking_common_length_common_sector_theorem`. None is proposed
for relocation.

## Whole-section and subsection inventory

“Inbound” lists later consumers of the indicated anchors. “Outbound” lists the
main immediate prerequisites. This is label-level evidence, rather than a
claim to enumerate every transitive Lean import.

### Chapter 1 — Introduction

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Chapter introduction | supporting/retain-for-flow | Anchors `ch:intro`, `eq:intro_canonical_form`, `eq:intro_matched_pair_gauge`; maps readers to `ch:mps`, `ch:single`, `ch:channels`, `ch:qpf`, `ch:spectral`, `ch:wielandt`, `ch:canonical`, `ch:bnt`, `ch:ft_proof`, and currently `ch:symmetry`. Retain; after relocating symmetry, remove its forward promise. |
| Notation | supporting/retain-for-flow | Uses the two displayed anchors above and establishes notation used across the retained route. Retain. |

### Chapter 2 — Matrix Product Vectors

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Basic definitions | essential | Defines `def:mps_tensor`, `def:eval_word`, `def:mpv`, `def:transfer_map`; inbound throughout Chapters 3--11. Retain. |
| Site-periodic tensor families | supporting/retain-for-flow | Defines `def:periodic_mps_tensor`, `def:periodic_relations`; no direct Chapter 11 use. Technically nonessential but short, and retains periodic vocabulary before later applications. Retain. |
| Gauge equivalence and same MPV | essential | Defines `def:gauge_equiv`, `def:same_mpv`, `def:same_mpv2_pos`, `def:gauge_phase_equiv`; inbound to Chapters 3, 7, 9--11. Retain. |
| Injectivity and normality | essential | Defines `def:injective`, `def:l_blk_injective`, `def:normal`; inbound to Chapters 3 and 7--10. Retain. |
| Canonical form | essential | Defines `def:block_diagonal_tensor`, `thm:mpv_decomposition`; inbound to Chapters 9--11. Retain. |
| Blocking | essential | Defines `def:blocked_tensor`, `lem:mpv_block`, `thm:blocking_same_mpv`; inbound to Chapters 8--11. Retain. |
| MPV overlap | essential | Defines `def:mpv_overlap`, `def:mpv_inner`; inbound to Chapter 7 and the BNT arguments. Retain. |

### Chapter 3 — The Single-Block Fundamental Theorem

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| The multiplicative linear extension | essential | Anchors `thm:trace_pairing_injective`, `lem:injectivity_transfer`, `thm:linear_ext`, `thm:linear_ext_mul`; outbound `def:injective`, `def:same_mpv`; feeds `thm:ft_single`. Retain. |
| Inner automorphism and the single-block theorem | essential | Anchors `thm:simplicity`, `thm:skolem_noether`, `thm:ft_single`; inbound to Chapter 7's gauge result and post-FT symmetry. Retain. |

### Chapter 4 — Quantum Channels and Positive Maps

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Positive maps and channels | supporting/retain-for-flow | Defines `def:positive_map`, `def:trace_preserving`, `def:cp_map`, Ky Fan tools, and channel data. Some reduction/Choi detail is broader than FT needs, but it is interleaved with the basic definitions used in Chapters 5--7. Retain as one section. |
| Irreducibility | essential | Anchors `def:irreducible_cp`, `thm:transfer_cp`, `thm:transfer_channel`; inbound to Chapters 6--9. Retain. |
| Cesàro fixed-point theorem | essential | Anchor `thm:cesaro_fixedpoint`; inbound to Chapter 6's `thm:psd_fp_exists`. Retain. |
| Fixed-point projection | essential | Anchors `def:fixed_point_proj`, `thm:pow_decomp`; inbound to Chapter 7 `thm:primitive_overlap`, then Chapters 8--9. Retain. |
| Peripheral spectrum and primitivity | essential | Anchors `def:peripheral_eigenvalues`, `thm:peripheral_finite`, `thm:peripheral_roots_of_unity`; outbound to period removal. Retain. |
| Periodicity removal by powering | essential | Anchors `lem:common_power_eq_one`, `lem:peripheral_pow_singleton`; inbound to Chapter 9 `thm:blocking_primitivity`. Retain. |
| Kadison--Schwarz inequality and multiplicative domain | essential | Anchors `thm:kadison_schwarz_channels`, `thm:kraus_commute_channels`, `thm:ks_peripheral_channels`; inbound to Chapters 4 and 7. Retain. |
| Peripheral closure via adjoint fixed point | essential | Anchors `thm:peripheral_roots_irred_fp`, `def:primitive_channel`, `thm:primitive_compl_lt_one`; inbound to Chapters 8--10, especially Chapter 9 period removal. Retain. |
| Fixed-point algebra | safe relocation candidate, coordinated cluster only | Anchors `def:kraus_fixed_points`, `thm:fixedPointsStarSubalgebra`, `thm:adjointFixedPointsStarSubalgebra`, `thm:adjointFixedPoints_eq_krausCommutant`. Its within-volume consumers are the movable Chapter 7 fixed-point sections; outbound Chapter 5 abstract-Schwarz labels. Move only with those sections. |

### Chapter 5 — Schwarz Inequalities and Multiplicative Domains

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Kadison--Schwarz inequality | essential | Defines the Kraus normalizations and `thm:kadison_schwarz`; feeds the retained multiplicative-domain and channel specialization arguments. Retain. |
| Two-positive maps and generalized Schwarz inequality | supporting/retain-for-flow | Contains `def:k_positive_map` and extensive Choi/Schmidt-rank material, but also `def:trace_pairing_adjoint` used by Chapter 4 normalization/fixed-point theory. It is not safe to move as one subsection. Retain. |
| The map $T_\eta$ and strictness of the chain | safe relocation candidate | Anchors `def:t_eta`, `thm:t_eta_threshold`, `cor:positivity_chain_strict`; consumers are local and Chapter 25's reduction criterion. Move to Chapter 25. |
| Positivity hierarchy and KS from two-positivity | safe relocation candidate | Anchor `thm:kadison_schwarz_2positive`; no retained FT-path consumer beyond direct `thm:kadison_schwarz`. Move with the $T_\eta$ subsection to Chapter 25. |
| Douglas-type factorization lemmas | essential | Includes `thm:ks_equality_of_peripheral_eigenvector_of_fixedPoint`, used in Chapter 7 cyclic decomposition. Retain as one unit. |
| Multiplicative domain | essential | Anchors `thm:ks_gap_decomp`, `thm:kraus_commute`, `thm:ks_peripheral`, `thm:left_multiplicative_identity`; inbound to Chapters 4 and 7. Retain. |
| Abstract Schwarz maps and their multiplicative domains | safe relocation candidate, coordinated cluster only | Anchors `def:abstract_schwarz_inequality`, `thm:abstract_md_characterization`; its direct consumer is Chapter 4 fixed-point algebra. Move only with that cluster. |
| Kraus specialization and full algebraic structure | safe relocation candidate, coordinated cluster only | Anchors `thm:md_characterization`, `thm:md_star_subalgebra`; feeds the same fixed-point cluster. Move with its predecessor and Chapter 4/7 fixed-point sections. |
| Schwarz inequality for normal operators | safe relocation candidate | Anchors `thm:ks_normal_cp`, `thm:schwarz_normal_operator`; only adjacent operator-theory consumers. Move to Chapter 18. |
| Schwarz inequality for subnormal and commuting-dominant operators | safe relocation candidate | Anchors `thm:schwarz_subnormal`, `thm:schwarz_commuting_dominant`; only local consumers. Move with the preceding subsection to Chapter 18. |
| Positive maps preserve order and spectral intervals | supporting/retain-for-flow | Anchors `thm:positive_map_monotone`, `thm:positive_map_conjTranspose`, and `thm:positive_map_spectrum_contractivity`. The retained Chapter 7 proof of `thm:maximalSupport_fixedPoint` explicitly uses `thm:positive_map_conjTranspose`; retain this whole subsection in Chapter 5 unless the fixed-point cluster is moved as a coordinated unit. |
| A positive Schwarz map that is not completely positive | safe relocation candidate | Anchors `def:wolf_example53`, `thm:wolf_example53_not_cp`; self-contained. Move to Chapter 25. |

### Chapter 6 — Perron--Frobenius Theory

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Positive definiteness | essential | `thm:psd_fp_pd`, `thm:psd_fp_pd_irred` are used in Chapters 6, 7, and 9. Retain. |
| Uniqueness | essential | `thm:psd_fp_unique`, `thm:psd_fp_unique_irred`, `thm:eigenvalue_unique_irred`; Chapter 11 uses the uniqueness route in the unitary equal case. Retain. |
| Existence and the PF theorem | essential | `thm:psd_fp_exists`, `thm:qpf`, `thm:qpf_irreducible`; Chapter 7 uses `thm:qpf`. Retain. |
| Right- and left-canonical gauges | essential | `thm:right_canonical_gauge`, `thm:left_canonical_gauge`; inbound to Chapters 7, 9, 10, and 12. Retain. |
| Similarity preserves irreducibility | supporting/retain-for-flow | `lem:similarity_irred`, `lem:similarity_irred_iff` bridge the next PF-eigenvector construction. Retain. |
| PF eigenvector existence | essential | `thm:pf_eigenvector_existence`, `thm:posDef_adjoint_eigenvector`, `thm:tp_data_irreducible`; inbound to Chapter 9. Retain. |
| Exponential positivity for irreducible CP maps | supporting/retain-for-flow | `thm:exp_truncation_pd_irred`, `thm:exp_pd_irred`; no direct Chapter 11 consumer. Retain as the short completion of the irreducibility-to-positivity story. |
| Ergodicity of irreducible channels | supporting/retain-for-flow | `thm:channel_density_fp_irred`, `thm:channel_cesaro_irred`; technically nonessential, but natural Wolf-derived interpretation of preceding results. Retain. |
| Spectral radius at the Perron eigenvalue | essential | `thm:spectral_radius_pf_irred` is used in Chapter 9 block normalization. Retain. |
| Spectral characterization of irreducibility | supporting/retain-for-flow | `def:has_spectral_properties`, `thm:irred_iff_spectral_properties`; no direct FT-path consumer. Retain as compact chapter endpoint. |

### Chapter 7 — Transfer-Operator Gaps and Block Separation

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Mixed transfer operator | essential | Defines `def:mixed_transfer`, `def:mixed_transfer_rect`, `thm:mixed_pow`; feeds all gap results. Retain. |
| MPV overlap as transfer trace | essential | `thm:overlap_trace`, `thm:overlap_trace_rect`; feeds BNT overlap arguments. Retain. |
| Frobenius norm estimates | essential | `def:frob_sq`, `lem:frob_sq_trace`; used by the eigenvalue bounds. Retain. |
| Eigenvalue bound and transfer-operator gap | essential | `thm:eigenvalue_bound`, `thm:modulus_one_gauge`, `thm:transfer_operator_gap`; outbound Chapters 3, 5, 6 and inbound later separation. Retain. |
| Rectangular transfer-operator gap | essential | `thm:transfer_operator_gap_rect`, `thm:overlap_decay_rect`; BNT needs rectangular separation. Retain. |
| MPV overlap decay | essential | `thm:transfer_pow_zero`, `thm:overlap_decay`; used by BNT separation. Retain. |
| Block separation | essential | `thm:cross_decay`, `thm:self_persist`; explains the canonical/BNT use. Retain. |
| Gap under irreducible-TP hypotheses | essential | `thm:modulus_one_gauge_irr_tp`, `thm:overlap_decay_irr_tp`, `thm:overlap_decay_rect_irr_tp`; inbound to Chapters 9--10. Retain. |
| Conditional expectation from a faithful fixed point | safe relocation candidate, fixed-point cluster | `def:is_conditional_expectation`, `def:scalar_conditional_expectation`; depends on the Chapter 4/5 fixed-point material, not Chapters 8--11. Move with the cluster. |
| Stationary support; faithful compression | safe relocation candidate, fixed-point cluster | `def:stationarySupport`, `thm:compression_on_support_posDef`, `thm:cornerFixedPointsStarSubalgebra`; feeds following Wedderburn work, not the FT spine. Move with the cluster. |
| Wedderburn decomposition of the fixed-point algebra | safe relocation candidate, fixed-point cluster | `thm:starSubalgebra_wedderburnArtin`, `thm:adjointFixedPoints_block_form`, `thm:fixedPoints_block_form`, `thm:wolf_6_14`; relevant to later channel/MPDO work. Move intact with the previous fixed-point sections. |
| Further irreducibility and primitivity equivalences | essential | `thm:wolf_6_8_conjunction` is used by Chapter 8 `thm:normal_from_primitive_posdef`. Retain. |
| Multi-cycle block-permutation structure | safe relocation candidate | `def:multi_cycle_decomposition`, `thm:multi_cycle_preserves_corner_pow_period`; no Chapter 8--11 consumer found. Move after the fixed-point cluster. |
| Peripheral eigenvalue group structure, including cyclic decomposition | essential | `thm:peripheral_cyclic_structure`, `thm:cyclic_decomposition_irreducible_schwarz`; Chapter 9 uses `thm:peripheral_cyclic_structure`. Retain. |
| Group structure of the peripheral spectrum | uncertain | `thm:peripheral_multiplicity_one` has no direct FT-path consumer, but is short and completes the preceding cyclic narrative. Retain. |
| Primitive overlap convergence | essential | `thm:trace_pow_one`, `thm:primitive_overlap`; inbound to Chapters 8--9. Retain. |

### Chapter 8 — Wielandt Bound

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Cumulative span | essential | Defines `def:word_span`, `def:cumulative_span`; feeds all later Wielandt results. Retain. |
| Fitting decomposition | supporting/retain-for-flow | `def:fitting_decomp`, `thm:nilpotent_pow_bound`; a readable finite-dimensional proof bridge. Retain. |
| Nonzero trace product | essential | `thm:cumulative_eq_top`, `thm:nonzero_trace_word`; feeds extraction and the bound. Retain. |
| Eigenvector extraction | essential | `thm:eigenvector_from_trace`, `thm:eigenvalue_extraction`; feeds blocked-span assembly. Retain. |
| Eigenvector spreading | essential | `thm:eigenvector_spreading`; feeds `thm:wielandt_lemma2b`. Retain. |
| Proof of the cumulative Wielandt bound | essential | `thm:wielandt_bound`, `thm:wielandt_general`; feeds exact blocking. Retain. |
| Fixed-length matrix spanning | essential | `thm:lemma2b_assembly`, `thm:bounded_injective_blocking_normal_left_canonical`; inbound to Chapter 10. Retain. |
| Blocked tensor and rectangular span | essential | `thm:wielandt_lemma2b`, `thm:isNormal_blockTensor`; completes fixed-length span. Retain. |
| Primitive MPS tensors and primitivity/normality subsections | essential | `def:primitive_mps`, `lem:primitive_implies_irreducible`, `thm:normal_from_primitive_posdef`; inbound to Chapter 9. Retain. |
| Cumulative span to word span | essential | `thm:cumspan_to_normal`, `thm:algspan_to_normal`; supports the normal/canonical route. Retain. |
| Block injectivity from TP/primitive/irreducible blocks | essential | `thm:tp_primitive_irred_block_injective`; direct Chapter 10 input. Retain. |

### Chapter 9 — Canonical Form Reduction

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Normal tensors and canonical forms; normalization conventions | essential | `def:nt_cpsv`, `sec:transfer_map_normalization`; establishes predicates used in Chapters 10--11. Retain. |
| Invariant-subspace decomposition; iterated reduction | essential | `thm:projector_closure_canonical_form`, `thm:irred_decomp`, `def:irreducible_tensor`, `thm:form_II`; feeds arbitrary-tensor reduction. Retain. |
| Normal canonical form; canonical form from primitivity | essential | `def:is_normal_canonical_form`, `thm:blocking_primitivity`; inbound to BNT construction. Retain. |
| Left-canonical/dual diagonalization; nonzero blocks/TP gauge | essential | `thm:CFII_data`, `thm:exists_normal_canonical_form`, `thm:tp_gauge_arbitrary`; feeds common blocking. Retain. |
| Blocking, period removal, and cyclic sectors | essential | `thm:common_blocking_period`, `thm:cyclic_sector_decomp_after_blocking`; uses Chapter 7 peripheral structure. Retain. |
| Reduction to primitive blocks | essential | `thm:ft_after_blocking_common_length_common_sector_theorem`, `thm:unconditional_common_primitive_irreducible_blocks`; direct Chapter 11 prerequisite. Retain. |
| Blocking and weighted direct sums | essential | `thm:block_tensor_to_tensor_from_blocks`, `thm:exists_common_blocked_cyclic_sector_family`, `thm:common_blocked_cyclic_sector_reindexed_nonzero_part`; direct BNT/FT transport. Retain. |

### Chapter 10 — Basis of Normal Tensors

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Bases of normal tensors | essential | `def:bnt`, `def:normal_cf_bnt`, `lem:eventual_coeff_eq_of_eventual_li`; the last is used in Chapter 11. Retain. |
| Permutation rigidity | essential | `thm:bnt_perm_same_card`, `thm:not_gauge_phase_eventually_not_proportional`; phase-separation bridge. Retain. |
| Newton--Girard and power-sum recovery | essential | `thm:power_sum_multiset`, `thm:bounded_power_sum_multiset`; feeds copy-weight recovery. Retain. |
| Sector decompositions and phase matching | essential | `def:sector_weight_data`, `def:sector_bnt_cf`, `lem:sector_bnt_combined_family_eventually_li`; defines Chapter 11 objects. Retain. |
| Prepared-block BNT construction | essential | `thm:paperbnt_supplier_after_blocking`, `thm:paperbnt_supplier_after_blocking_normalized`; connects Chapter 9 to BNT. Retain. |
| Matched-sector weight multiset equality | essential | `lem:sector_bnt_matched_sector_weight_multiset_eq`, `lem:sector_bnt_matched_sector_weight_equiv`; Chapter 11 input. Retain. |
| Strong matching and bijective matching | essential | `thm:sector_bnt_exact_block_match`, `thm:sector_bnt_bijective_match_of_sameMPV`; explicitly invoked by Chapter 11. Retain. |

### Chapter 11 — Proof of the Fundamental Theorem

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Coefficient identity, copy weights, and block-diagonal gauge | essential | `thm:sector_bnt_proportional_global_gauge_of_coeff_identity`, `thm:sector_bnt_equal_global_gauge`, `thm:sector_bnt_equal_mps_gaugeEquiv_literal`; target proof. Retain. |
| Equal and proportional cases | essential | `thm:cpgsv_multiblock_ft_source`, `thm:cpgsv_equal_case_source`; finishes the stated source cases. Retain. |

### Chapter 12 — Symmetries and String Order

| Unit | Class | Label evidence and recommendation |
|---|---|---|
| Physical symmetries give virtual gauges | safe relocation candidate | `def:rotate_physical`, `cor:symmetry_periodic_assembly`; only later periodic-FT material uses `def:rotate_physical`. Move with the whole chapter. |
| Virtual representation theorem | safe relocation candidate | `def:on_site_symmetric`, `thm:virtual_rep_injective`; outbound `thm:ft_single`, so it is an application. Move with the whole chapter. |
| Cohomology classes; commutator-phase non-triviality | safe relocation candidate | `def:cohomologous_to`, `def:h2_cx`, `thm:cocycle_gauge_independence`, `thm:nontrivial_of_comm_phase`; consumed only by symmetry/SPT material. Move with the whole chapter. |
| Permutation-based physical symmetry | safe relocation candidate | `def:on_site_symmetry_perm`, `def:perm_twisted_tensor`; local bridge to string order. Move with the whole chapter. |
| String order and local symmetry equivalence | safe relocation candidate | `def:has_string_order`, `thm:string_order_iff_local_symmetry`; uses retained Chapter 7 gap results but does not feed Chapter 11. Move with the whole chapter. |
| SPT phase labels and string-order universality | safe relocation candidate | `def:is_same_spt_phase`, `thm:has_string_order_iff_of_symmetric_injective`; culmination of the post-FT application. Move with the whole chapter. |

## Technically nonessential units retained for flow

The following should remain in this first pass despite a narrow nonessential
argument: Chapter 2 site-periodic families; Chapter 4 positive maps and
channels; Chapter 5 two-positive/generalized-Schwarz material (because it
also houses trace-adjoint infrastructure); Chapter 6 similarity, exponential
positivity, ergodicity, and spectral characterization; Chapter 7 peripheral
multiplicity; and Chapter 8 Fitting decomposition. They preserve the local
Wolf narrative or package indispensable material with broader context.

## Conservative proposed relocation map

| Priority | Move | Destination | Rationale |
|---|---|---|---|
| 1 | Entire `ch12_symmetry.tex` | Immediately after the Fundamental Theorem, before Parent Hamiltonians, as the first post-FT application chapter. | All of Chapter 12 is downstream of the theorem. The dedicated FT volume becomes an 11-chapter route. |
| 2 | Chapter 5: $T_\eta$, positivity hierarchy, and positive-Schwarz-not-CP subsections | Chapter 25, “Positive but Not Completely Positive Maps.” | Chapter 25 already relies on `def:t_eta` and explicitly describes this subject. |
| 3 | Chapter 5: normal-operator and subnormal/commuting-dominant subsections | Chapter 18, “Operator Convexity and Jensen Inequalities,” before Jensen material. | These are stand-alone operator-theory consequences with no FT consumer. Retain the adjacent order/spectral-interval subsection in Chapter 5 because Chapter 7 uses its adjoint-preservation theorem. |
| 4 | Coordinated fixed-point cluster: Chapter 4 fixed-point algebra; Chapter 5 abstract Schwarz plus Kraus specialization; Chapter 7 from conditional expectation through Wedderburn; Chapter 7 multi-cycle structure | Expand Chapter 16 into “Channel Representations, Fixed Points, and Normal Forms.” | Preserves the local chain abstract Schwarz $\to$ fixed-point algebra $\to$ support compression $\to$ Wedderburn $\to$ multicycle structure, while removing a large non-FT detour. |

Priority 4 is optional and should follow successful priority 1--3 builds. Do
not move Chapter 7 “Further irreducibility and primitivity equivalences,”
“Peripheral eigenvalue group structure” (including cyclic decomposition), or
“Primitive overlap convergence”: they are actual Chapter 8--10 inputs.


## Implementation status (2026-07-19)

The conservative priorities were implemented as follows.

| Priority | Status | Record |
|---|---|---|
| 1 — Focused FT route | completed | `content_ft_mps.tex` now ends with `ch11_fundamental_theorem_proof`; `ch12_symmetry.tex` remains immediately after Chapter 11 in `content.tex`.  The historical build-script filename and `print12.pdf` artifact were retained, but its router contract, diagnostics, README description, and Chapter 1 route prose now describe the focused Chapters 1--11 volume. |
| 2 — Positive/non-CP material | completed | The intact Chapter 5 subsections on $T_\eta$, the positivity hierarchy, and the positive Schwarz non-CP example now appear in Chapter 25.  Labels, Lean annotations, proofs, and their order within each moved cluster were preserved. |
| 3 — Operator-theory Schwarz material | partially completed | The intact Chapter 5 subsections on normal operators and on subnormal/commuting-dominant operators now precede Jensen material in Chapter 18.  The complete “Positive maps preserve order and spectral intervals” subsection was retained in Chapter 5: `thm:positive_map_conjTranspose` is an explicit dependency of Chapter 7 `thm:maximalSupport_fixedPoint`.  Labels, Lean annotations, and internal ordering were preserved for the moved material. |
| 4 — Fixed-point/Wedderburn cluster | deferred | Chapter 4 fixed-point algebra, Chapter 5 abstract multiplicative-domain material, and Chapter 7 stationary-support/Wedderburn material remain in place. |

## Validation risks

1. **Router contract:** after priority 1, change `content_ft_mps.tex`,
   `scripts/build_blueprint_ch01_12.sh`, `blueprint/README.md`, and Chapter 1
   references together. The present script rejects any list other than
   the focused `ch01..ch11` route.
2. **Standalone references:** the dedicated build script warns that references
   into dropped chapters render `??`. Remove Chapter 1's reference to
   `ch:symmetry` from the standalone narrative, and inspect the PDF.
3. **Fixed-point cluster:** never move Chapter 7 support/Wedderburn sections
   without Chapter 4 `thm:adjointFixedPointsStarSubalgebra` infrastructure and
   Chapter 5 `thm:abstract_md_characterization`; their current labels cross
   that boundary.
4. **Re-audit before priority 4:** recent Channel/FixedPoint changes touched
   Chapter 7. Recheck `\uses{}`, `\ref{}`, and `\lean{}` targets immediately
   before editing.
5. **Build/check each step:** build the full blueprint and the dedicated
   FT volume, then check declarations. Inspect unresolved references in both
   outputs.
6. **Proof status is out of scope:** this audit changes neither `\lean{}`
   links nor `\leanok`/source-gap status.

## Implementation validation record (2026-07-19)

- The focused build command `./scripts/build_blueprint_ch01_12.sh` completed
  successfully after the relocation and wrote
  `blueprint/print/print12.pdf`. Its router check confirmed the exact,
  duplicate-free `ch01`--`ch11` sequence. The compiler reports 20 unresolved
  dependency/link entries into omitted full-volume chapters; PDF text inspection
  exposes three visible numbered references: `thm:choi_transpose_flip`,
  `ch:parent_hamiltonian`, and `thm:sharp_bnt_block_separation`. These are
  pre-existing forward references from the focused route into later full-volume
  chapters; none was introduced by this relocation.
- `leanblueprint checkdecls` was attempted, but could not start its declaration
  check because the existing Lean object
  `TNLean.Entropy.StrongSubadditivity.olean` was absent.
- A subsequent `lake build` attempt did not complete: its first run failed on
  missing generated Channel object files, and a retry exceeded the available
  ten-minute command limit. Consequently declaration checking could not be
  completed in this session.
- The full PDF build `cd blueprint && leanblueprint pdf` completed successfully
  in an uninterrupted detached run. It produced a 674-page
  `blueprint/print/print.pdf`; the final log contains no unresolved-reference,
  unresolved-citation, or LaTeX-error diagnostics. PDF text inspection
  confirmed the relocated Chapter 18 and Chapter 25 section headings and the
  positive-Schwarz example are present.
- Short final checks passed: the focused router has exactly eleven inputs,
  every moved/retained subsection heading occurs once in the chapter sources,
  `bash -n scripts/build_blueprint_ch01_12.sh` succeeds, and `git diff --check`
  is clean.

## Conclusion

The lowest-risk improvement is to end the FT--MPS volume at Chapter 11 and
move Chapter 12 intact to the post-FT material. The next safe reductions are
the identified Chapter 5 application subsections. The stationary-support and
Wedderburn material is also outside the FT dependency spine, but should move
only as the coordinated Chapter 4/5/7 fixed-point cluster. All remaining
Chapters 1--11 units should remain in place under this conservative policy.
