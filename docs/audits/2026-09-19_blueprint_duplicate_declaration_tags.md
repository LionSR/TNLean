# Duplicate blueprint declaration tags

Issue #7855. The ownership convention of
`docs/audits/2026-08-20_blueprint_declaration_ownership.md` gives every Lean
declaration exactly one blueprint entry carrying its `\lean{...}` tag; a later
specialization, application, or recap cites that owner through `\uses`. A census
of `blueprint/src` found 9,014 tag references over 8,967 distinct declarations,
with 46 declarations tagged in more than one entry. This pass resolves the 30
pairs that predate the asymmetric-examples chapter: it removes the second tag of
each, adds the citing edge in its place, discharges the two dependency edges the
2026-08-20 note deferred, and adds a checker mode so the convention can be
measured rather than restated. The remaining 17, all of them recaps introduced
with that chapter, are listed at the end.

No Lean source, theorem statement, or proof was changed. Every declaration named
below keeps a `\lean{...}` tag in its owning entry, so the set of tagged
declarations is unchanged and no formalization status moves.

## Why the earlier exemption no longer applies

The 2026-08-20 note deferred two dependency edges because Chapters 23 and 24 were
excluded from `blueprint/src/content.tex`, which made an edge into either chapter
unresolvable. Both chapters are now inputs of `content.tex`, and all 250 sources
reachable from it include every file touched here, so both edges are now
representable and were added:

- the Chapter 21 per-block linear extension cites the Chapter 23 definition at
  statement level, and its multiplicativity, bijectivity, and
  unitary-implementation results cite the corresponding Chapter 23 results at
  proof level;
- the Chapter 24 identification of cycle-tensor state coefficients cites the
  Chapter 13 cyclic trace expansion at proof level.

## Tags removed and their surviving owners

| Declaration | Owning entry | Entry that relinquished the tag |
|---|---|---|
| `Kraus.mixedMapLM` | `def:mixed_transfer_rect` | `def:mixed_transfer` |
| `Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily` | `thm:transfer_map_irreducible_of_tensor` | `thm:irreducible_tensor_to_transfer_map` |
| `MPOTensor.basis_opposite_insert_eq_of_rotated_mpo_entries` | `thm:blockwise_opposite_insert_rotated_mpo` | `thm:representative_one_sub_mp_zero` |
| `MPOTensor.blockTensor_mulTensor` | `thm:mpdo_blocking_product` | `thm:mpug_common_blocking_representation` |
| `MPOTensor.mpo_blockTensor_eq_reindex` | `thm:mpdo_closed_chain_physical_blocking` | `thm:mpug_common_blocking_representation` |
| `MPOTensor.siteSign` | `def:cpsv_example412_site_sign` | `thm:kato_deformed_mpdo_fixed_tensor_obstruction` |
| `MPOTensor.configurationSign` | `def:cpsv_example412_configuration_sign` | `thm:kato_deformed_mpdo_fixed_tensor_obstruction` |
| `MPOTensor.isSAL_of_isRFPViaTS_of_trace_ne_zero` | `thm:mpdo_rfp_implies_sal` | `thm:mpdo_rfp_implies_zcl_and_sal` |
| `MPOTensor.isSAL_of_isRFPViaTS` | `cor:mpdo_horizontal_rfp_implies_sal` | `cor:mpdo_horizontal_rfp_implies_zcl_and_sal` |
| `MPOTensor.physTraceTransfer_sq_of_isRFPViaTS` | `thm:mpdo_rfp_implies_zcl_and_sal` | `cor:mpdo_horizontal_rfp_implies_zcl_and_sal` |
| `MPOTensor.trace_mpo_changePhysicalBasis_of_isometry` | `thm:mpdo_sal_physical_isometry_transport` | proof of `thm:mpdo_normalized_state_physical_isometry_transport` |
| `MPOTensor.weighted_basis_physTraceTransfer_sq_of_literal_ZCL` | `lem:mpdo_simple_blockwise_zcl_equation` | `thm:mpdo_absorbed_bnt_sector_literal_zcl` |
| `MPSChainTensor` | `def:periodic_mps_tensor` | `def:non_ti_chain` |
| `MPSChainTensor.SameState` | `def:periodic_relations` | `def:non_ti_chain` |
| `MPSChainTensor.GaugeEquiv` | `def:periodic_relations` | `def:non_ti_chain` |
| `MPSTensor.groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1_pgvwc07` | `thm:pgvwc_block_space_independence_doubly_normalized` | `thm:bnt_block_diagonal_open_boundary_matrices_source_length_doubly_normalized` |
| `MPSTensor.isNBlkInjective_of_le` | `thm:wordspan_blk_inj_succ` | `lem:isNBlkInjective_of_le` |
| `MPSTensor.leftCanonical_reindexPhysical_equiv` | `thm:cpsv_physical_reindexing` | `thm:mpu_left_canonical_blocking_reindexing` |
| `MPSTensor.rotatePhysical` | `def:rotate_physical` | `def:physical_rotation` |
| `MPSTensor.mpv_rotatePhysical` | `lem:mpv_rotate_physical` | `lem:physical_rotation_state` |
| `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound` | `lem:parent_hamiltonian_cyclic_overlap_norm_gap` | `thm:overlap_norm_gap_bound` |
| `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_anticommutator` | `lem:parent_hamiltonian_cyclic_overlap_anticommutator_gap` | `thm:anticommutator_gap_bound` |
| `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_lt` | `lem:parent_hamiltonian_cyclic_overlap_norm_constant_gap` | `thm:overlap_norm_gap_bound_constant` |
| `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_operator_norm_of_lt` | `lem:parent_hamiltonian_cyclic_overlap_operator_norm_constant_gap` | `thm:overlap_operator_norm_gap_bound_constant` |
| `TNLean.PEPS.fundamentalTheorem_normalTorusPEPS_unconditional` | `thm:fundamentalTheorem_normalTorusPEPS_unconditional` | `thm:fundamentalTheorem_normalTorusPEPS` |
| `TNLean.PEPS.torusAbsorbedGauge_unique_scalar` | `thm:torusAbsorbedGauge_unique_scalar` | `thm:fundamentalTheorem_normalTorusPEPS` |
| `TNLean.PEPS.torusCovariantAbsorbedGauge_unique_classScalar` | `thm:torusCovariantAbsorbedGauge_unique_classScalar` | `thm:fundamentalTheorem_normalTorusPEPS` |
| `TNLean.PEPS.torusGauge_unique_scalar_of_perVertex` | `thm:torusGauge_unique_scalar_of_perVertex` | `thm:fundamentalTheorem_normalTorusPEPS` |
| `finTupleProdEquiv` | `def:mps_independent_tensor_product` | `def:mpu_independent_tensor_product` |
| `SpinChain.disjoint_leftPair_rightPair` | `lem:qca_nearest_neighbor_pair_geometry` | `lem:qca_consecutive_pair_geometry` |

Each relinquishing entry now reaches its owner through `\uses`, at statement
level when the owned result is needed to formulate the statement and at proof
level when the argument uses it. Six entries already carried the edge, so only
the tag line was removed there: the two horizontal area-law nodes, the four
martingale recaps of the cyclic-overlap gap bounds, and the block-diagonal
boundary theorem, whose proof already cited the block-space independence
theorem.

## Ownership choices that needed a judgement

Three pairs were resolved against the direction first proposed, in each case
towards the entry whose statement is the declaration rather than the entry that
bundles it with others.

- `MPOTensor.trace_mpo_changePhysicalBasis_of_isometry` was tagged both in the
  statement of the area-law transport theorem and inside the *proof* of the
  normalized-operator theorem. A tag inside a proof body is not an entry, and
  only four such tags exist in the whole blueprint, so the proof-body tag was
  removed and statement-level ownership kept. The proof establishes the trace
  identity inline and needs no new edge.
- `MPSTensor.groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1_pgvwc07` is
  the block-space independence statement. The boundary-condition theorem that
  also tagged it already cites the independence theorem in its proof, which
  fixes the dependency direction, so the independence entry keeps the tag.
- `MPOTensor.basis_opposite_insert_eq_of_rotated_mpo_entries` was tagged both in
  the eleven-declaration first-site-contraction entry and in the dedicated entry
  stating exactly that reduction. The dedicated entry keeps the tag; the
  bundling entry now cites it and retains its ten other tags.

## What is retained

- The rectangular mixed transfer operator entry is retained as the owner, with
  the square entry citing it: the rectangular map is the general one and has the
  larger set of citation sites.
- The four martingale gap-bound entries are retained in full. They are cited by
  ten surrounding `\uses` and `\ref` sites, and the minimal fix for the
  convention is the removal of four tag lines, not the removal of narrative.
- Entries that relinquished a tag keep `\leanok`, matching the shape the
  2026-08-20 pass left behind for the per-block linear extension entries.
- Eleven of the thirty declarations sit in entries that state a conjunction of
  several formalized results: the four torus results, the three renormalization
  fixed-point area-law results, the two Pauli-sign definitions, and the two
  blocking results. These follow the multi-anchor remediation recorded under
  issue #7726: the tag is dropped, the proof-level or statement-level `\uses`
  edge is kept, and `\leanok` stays.

## Verification

- The census is reproducible with `scripts/blueprint_lean_sync.py` through
  `collect_blueprint_lean_refs` and `find_duplicate_lean_tags`: 9,014 references
  over 8,967 declarations with 46 duplicated declarations before this pass,
  8,984 references over the same 8,967 declarations with 17 after it. Every
  declaration keeps a tag, so the tagged set is the same on both sides.
- `python3 scripts/blueprint_lean_sync.py --root . --ci` passes, and the same
  command with `--report-duplicate-tags` lists the 17 remaining pairs.
- `python3 scripts/test_blueprint_lean_sync.py` passes, including a new test of
  the duplicate finder.
- Every label added to a `\uses` list resolves to exactly one `\label` in the
  sources reachable from `content.tex`, and none of the 24 added edges closes a
  cycle in the dependency graph.
- `git diff --check` passes.

## Enforcement and what is deferred

`scripts/blueprint_lean_sync.py` gained a `--report-duplicate-tags` flag. Every
run now lists declarations tagged in more than one entry; with the flag and
`--ci`, such a declaration fails the run. Making the blueprint job pass the flag
is deliberately left for a follow-up, because 17 further pairs arrived with the
asymmetric-examples chapter and would fail the job today. All 17 sit in
`ch25_asymmetric_examples_rfp.tex`, which recaps entries of Chapter 21: thirteen
twisted-dimer declarations and one rescaling declaration owned by
`ch21_mpdo_rfp_bnt_coefficients_dimer.tex` and
`ch21_mpdo_rfp_bnt_coefficients_rescaling.tex`, two fusion-clause equivalences
owned by `ch21_mpdo_rfp_fusion_isometries_product_laws.tex`, and
`MPOTensor.physTraceTransfer_sq_of_isRFPViaTS`, which that chapter tags
alongside its Chapter 21 owner. Resolving them the same way and then passing the
flag in the blueprint job is the next step. Without it the convention keeps
drifting: two of the thirty pairs closed here were introduced after it was
recorded, and the 17 arrived a month later.

The conjunction-entry pairs remain evidence for the multi-anchor discussion under
issue #7726, which decides whether such entries should carry a machine-readable
link of their own; if it introduces one, the eleven entries listed above are its
first consumers.
