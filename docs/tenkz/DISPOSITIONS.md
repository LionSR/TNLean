# tenkz migration dispositions

This inventory is the migration ledger for issue #4748. It classifies the
tracked tree at commit `c40b923493f29aa75799810ed297193526da51df`
against the signed 1.0 contract in `LANGUAGE-1.0.md` §§9–12. The
classification concerns the S4 surface switch, not whether a figure is
mathematically or visually correct today. The committed disposition checker
keeps the line inventory, fixture lists, and reconciliation tables synchronized
with the tracked TeX sources.

## Disposition rules

- **Preserve** means a pure `tenkz` grid construct already uses kernel
  vocabulary. It remains byte-compatible at the surface switch.
- **Codemod** means every non-kernel spelling has a mechanical expansion in
  the §9 sugar ledger or an exact 0.7 atom-shorthand respelling to 1.0 atom
  keys. The target codes below name that expansion.
- **Redraw** means the construct depends on a §10 tombstone. Its mathematical
  boundary and topology must be re-authored with the named §12-style shape;
  a compatibility-renderer transcription is not a migration.
- A fixture receives its most demanding disposition: redraw outranks codemod,
  which outranks preserve. A fixture with no picture construct is preserved
  because it has no surface-switch consumer.

### Migration target codes

| Code | Required 1.0 target |
|---|---|
| `P-grid` | Keep the existing pure-kernel `tenkz` grid spelling byte-compatible. |
| `C-picture` | Expand `\tnpic` to a scoped `tenkz` picture term. |
| `C-tree` | Expand `\tntree` to declared fuse atoms and `\tnwire` records. |
| `C-policy` | Expand physical/boundary sugar to `rows=`, typed `ports=`, and explicit side policies. |
| `C-frame` | Expand lattice/ring/surface/planes/cluster sugar to rows, columns, frame, basis members, and explicit closures. |
| `C-record` | Expand atom, wire, span, skip, and port sugar; respell 0.7 atom flags as `skin=` and typed `ports=` on `\tn`, `\tnwire`, and `\tnmark` records. |
| `C-species` | Replace `role=` with the corresponding declared `species=`. |
| `R-free` | Redraw the free graph as addressed `\tn`, `\tnwire`, and `\tnmark` records; §12.7 is the canonical irregular addressed-graph shape. |
| `R-cd` | Use external `tikz-cd` for a commutative map, or redraw tensor/fusion content as `tenkz` records and equation composition. |
| `R-lattice` | Redraw as a flat-frame `tenkz` lattice: rows/columns for regular members, or a declared basis for staggered/cluster members (§12.5). |
| `R-plane` | Redraw as a `tenkz` plane frame with declared basis members and ordinary addressed records. |
| `R-record` | Replace tombstoned commands, keys, routes, labels, or aliases with their exact §10 migration (`\tn`, `\tnwire`, `\tnmark`, `ports=`, `route=`, `label pos=`, `species=`). |

## Blueprint inventory

The source root for every path in this table is `blueprint/src/chapter/`.
Every environment opening and every `\tnpic` or `\tntree` occurrence is
listed by its tracked line. A command nested inside an environment is a
separate public-surface occurrence and therefore appears separately.

| Source | Preserve | Codemod | Redraw |
|---|---|---|---|
| `ch02_mps.tex` | — | L24, 54, 171, 200, 272, 941 `tenkz` → `C-policy+C-record` | L815 `tenkz` → `R-record` |
| `ch03_single.tex` | — | L250 `tenkz` → `C-policy+C-record` | — |
| `ch04_channels_choi_foundations.tex` | — | — | L86 `tenkz` → `R-record` |
| `ch11_fundamental_theorem_core.tex` | — | L41, 45 `tenkz` → `C-policy+C-record` | — |
| `ch12_symmetry_string_order.tex` | — | L367, 513, 871 `tenkz` → `C-policy+C-record`<br>L396, 410, 453, 468, 549, 563 `tenkz` → `C-record` | L39, 73, 352, 499, 866 `tenkz` → `R-record` |
| `ch12_symmetry_virtual_and_cohomology.tex` | — | L195, 328, 456, 469 `tenkz` → `C-policy+C-record` | L180 `tenkz` → `R-record` |
| `ch13_parent_hamiltonian_commuting_gap_appendix_b_commutation.tex` | — | — | L54 `tenkzfree` → `R-free+R-record` |
| `ch13_parent_hamiltonian_commuting_gap_appendix_b_supports.tex` | — | — | L275 `tenkzfree` → `R-free+R-record` |
| `ch13_parent_hamiltonian_injective_ground_spaces_intersection_property.tex` | — | L97 `tenkz` → `C-policy+C-record` | — |
| `ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex` | — | L35, 489, 528 `tenkz` → `C-policy+C-record` | — |
| `ch14_correlations.tex` | — | — | L67 `tenkz` → `R-record` |
| `ch16_channel_representations_choi_and_kraus.tex` | — | L290 `tenkz` → `C-policy+C-record` | — |
| `ch16_channel_representations_dilations_and_ordered_cp.tex` | — | L20 `tenkz` → `C-policy+C-record` | — |
| `ch20_mpdo_canonical_forms_first_site_contractions.tex` | — | L232, 238, 336 `tenkz` → `C-policy+C-record` | L153, 159, 177, 182, 433 `tenkz` → `R-record` |
| `ch20_mpdo_canonical_forms_intro_finite_separation.tex` | — | L104 `tenkz` → `C-policy`<br>L108 `tenkz` → `C-policy+C-record` | L218 `tenkz` → `R-record`<br>L224, 359, 391, 465 `tenkzfree` → `R-free+R-record` |
| `ch20_mpdo_canonical_forms_positivity_gram_normalization.tex` | — | — | L605, 610 `tenkz` → `R-record` |
| `ch20_mpdo_foundations.tex` | — | L16, 124 `tenkz` → `C-policy+C-record` | L370, 374 `tenkz` → `R-record` |
| `ch21_mpdo_rfp_algebra_tower.tex` | — | — | L78, 93 `tenkz` → `R-record` |
| `ch21_mpdo_rfp_blocked_rfp_positive_blocking_and_sector_algebra.tex` | — | — | L18, 21 `tnpic` → `C-picture+R-record` |
| `ch21_mpdo_rfp_foundations.tex` | — | L63, 67 `tenkz` → `C-policy+C-record` | — |
| `ch21_mpdo_rfp_fusion_isometries_complete_zipper_coherence.tex` | — | L215, 219, 292, 293, 294, 295, 296 `tntree` → `C-tree` | L291, 410 `tenkzcd` → `R-cd+R-record` |
| `ch21_mpdo_rfp_fusion_isometries_fixed_final_comparison.tex` | — | L572, 577 `tntree` → `C-tree` | — |
| `ch21_mpdo_rfp_fusion_isometries_foundations.tex` | — | L400, 641, 654, 669 `tnpic` → `C-picture+C-record`<br>L407 `tnpic` → `C-picture+C-policy+C-record` | L647, 661, 674 `tnpic` → `C-picture+R-record` |
| `ch21_mpdo_rfp_fusion_isometries_product_laws.tex` | — | L420, 422 `tntree` → `C-tree` | L38, 50 `tnpic` → `C-picture+R-record`<br>L283 `tenkzfree` → `R-free+R-record` |
| `ch21_mpdo_rfp_renormalization.tex` | — | — | L734 `tenkzcd` → `R-cd+R-record`<br>L736, 739, 742, 745 `tnpic` → `C-picture+R-record` |
| `ch21_mpdo_rfp_simple_local_closed_sector_contractions.tex` | — | L284 `tenkz` → `C-policy+C-record` | L279 `tenkz` → `R-record` |
| `ch21_mpdo_rfp_simple_local_inverse_map_factorization.tex` | — | L131 `tenkz` → `C-policy+C-record`<br>L485 `tnpic` → `C-picture+C-policy+C-record` | L43, 48, 53, 70, 80, 265, 270, 275, 282, 287, 709, 715, 719 `tenkz` → `R-record` |
| `ch21_mpdo_rfp_simple_local_neighboring_bond_contractions.tex` | — | — | L731, 740, 747, 754, 827, 833 `tenkz` → `R-record` |
| `ch21_mpdo_rfp_simple_local_normalized_preparations_controlled_partial_traces.tex` | — | — | L427 `tenkzcd` → `R-cd+R-record` |
| `ch21_mpdo_rfp_simple_local_primitivity_active_trace_matrix.tex` | — | — | L188 `tenkz` → `R-record` |
| `ch21_mpdo_rfp_simple_local_refinement_channels_physical_coordinates.tex` | — | — | L324, 329, 334, 344, 352, 357 `tnpic` → `C-picture+R-record` |
| `ch21_mpdo_rfp_simple_local_refinement_channels_sector_coordinates.tex` | — | — | L160, 175 `tenkzcd` → `R-cd+R-record` |
| `ch21_mpdo_rfp_simple_local_structure_capstone.tex` | — | L259 `tenkz` → `C-record`<br>L443 `tenkz` → `C-policy+C-record` | L447, 453, 458 `tenkz` → `R-record` |
| `ch23_algebraic_ft_foundations.tex` | — | L47, 51, 167, 371, 375, 387, 391, 433, 437, 441, 450, 454 `tenkz` → `C-policy+C-record` | L171 `tenkz` → `R-record` |
| `ch24_peps_ft.tex` | — | — | L25 `tenkzlattice` → `R-lattice+R-record`<br>L53, 96 `tenkzfree` → `R-free+R-record` |
| `ch24_peps_ft_balanced_edge_scalars.tex` | — | — | L18 `tenkzfree` → `R-free+R-record` |
| `ch24_peps_ft_edge_kernel_gauges_absorption_scalar_comparison.tex` | — | — | L83, 115, 316, 329, 347, 365, 623, 647 `tenkzfree` → `R-free+R-record` |
| `ch24_peps_ft_edge_kernel_gauges_insertion_algebra_local_gauges.tex` | — | L52, 56 `tnpic` → `C-picture+C-policy+C-record` | — |
| `ch24_peps_ft_edge_kernel_gauges_kernel_descent_recovery.tex` | — | — | L174, 196, 218, 445, 467, 489 `tenkzfree` → `R-free+R-record` |
| `ch24_peps_ft_edge_middle.tex` | — | L278 `tnpic` → `C-picture+C-policy` | L242 `tenkzfree` → `R-free+R-record` |
| `ch24_peps_ft_foundations.tex` | — | — | L48, 384 `tenkzfree` → `R-free+R-record` |
| `ch24_peps_ft_normal_capstone_normal_peps.tex` | — | — | L43, 67, 73 `tenkzlattice` → `R-lattice+R-record` |
| `ch24_peps_ft_normal_square_blocking_and_fundamental.tex` | — | — | L21, 28, 89, 95, 114, 150 `tenkzlattice` → `R-lattice+R-record`<br>L162, 212, 229 `tenkzfree` → `R-free+R-record` |
| `ch24_peps_ft_normal_square_coordinate_regions.tex` | — | — | L99, 104, 121, 286 `tenkzlattice` → `R-lattice+R-record` |
| `ch24_peps_ft_normal_square_rectangular_injectivity.tex` | — | — | L205, 214 `tenkzlattice` → `R-lattice+R-record` |
| `ch24_peps_ft_normal_square_translated_windows_and_comparison.tex` | — | — | L380 `tenkzlattice` → `R-lattice+R-record` |
| `ch24_peps_ft_normal_union.tex` | — | — | L213, 270, 301, 327, 358 `tenkzfree` → `R-free+R-record` |
| `ch24_peps_ft_region_transfer_covariance.tex` | — | L350, 354, 358, 362 `tnpic` → `C-picture+C-policy` | — |
| `ch24_peps_ft_torus_translation_and_reference_windows.tex` | — | — | L22 `tenkzlattice` → `R-lattice+R-record` |
| `ch26_mps_rfp_normal_isometry_canonical_forms.tex` | — | L452, 456 `tenkz` → `C-policy+C-record` | L580 `tenkz` → `R-record`<br>L585 `tenkzfree` → `R-free+R-record` |
| `ch26_mps_rfp_physical_blocking.tex` | — | L130, 155 `tenkz` → `C-policy+C-record` | L134, 149 `tenkz` → `R-record` |

### Blueprint reconciliation

| Raw construct | Occurrences |
|---|---:|
| `tenkz` | 106 |
| `tenkzfree` | 36 |
| `tenkzlattice` | 18 |
| `tenkzcd` | 6 |
| `tenkzplanes` | 0 |
| `tnpic` | 30 |
| `tntree` | 11 |
| **Total** | **207** |

| Disposition | Occurrences |
|---|---:|
| preserve | 0 |
| codemod | 81 |
| redraw | 126 |
| **Total** | **207** |

The raw count is 166 environment openings plus 41 command occurrences,
which reconciles to 207. This reproduces the issue baseline: 106 `tenkz`,
36 `tenkzfree`, 18 `tenkzlattice`, 6 `tenkzcd`, 0 `tenkzplanes`,
and 41 `\tnpic`/`\tntree` lines.

## Standalone fixture inventory

The source root for every file below is `tests/tenkz/`. Classification is
whole-fixture so the list decides whether each top-level corpus file is
retained, mechanically respelled, or redrawn/re-baselined at S4.

| Disposition | Fixtures |
|---|---:|
| preserve | 13 |
| codemod | 51 |
| redraw | 200 |
| **Total** | **264** |

Of the 264 top-level fixtures, 245 open at least one tenkz
environment, 11 are command-only consumers, and 8
contain no picture construct. Multiple pictures in one file account for the
770 occurrence total.

### Preserve fixtures (13)

- `geom.tex` · `iso_h.tex` · `modes_dot_baseline.tex` · `p3_probe_opop.tex` · `p_pitch.tex` · `p_species.tex` · `plane_experiment.tex` · `rv4061_flatonly.tex`
- `trace_warn.tex` · `zz_geomdag.tex` · `zz_geomframe.tex` · `zz_geomsupport.tex` · `zz_wirescan.tex`

### Codemod fixtures (51)

- `audit3.tex` · `audit4.tex` · `channel_test.tex` · `g06_stageB.tex` · `gr_t2_fsymbol.tex` · `hard01_v2.tex` · `hard02_v2.tex` · `hard11_v2.tex`
- `hard11_v3.tex` · `hard11_v4.tex` · `hdr.tex` · `iso_a.tex` · `iso_b.tex` · `iso_c.tex` · `iso_d.tex` · `iso_e.tex`
- `iso_f.tex` · `iso_g.tex` · `iso_i.tex` · `iso_j.tex` · `iso_k.tex` · `iso_t.tex` · `lrbox_probe.tex` · `p3_bisect_a.tex`
- `p3_bisect_d.tex` · `p3_bond_insertion.tex` · `p3_eq5_fsymbol.tex` · `p3_eq5_v2.tex` · `p3_gauge.tex` · `p3_lemma1.tex` · `p3_pitch_probe.tex` · `p3_trace_word.tex`
- `p3_word.tex` · `p4067_braced.tex` · `p_newcup.tex` · `part_B1.tex` · `part_B2.tex` · `part_B3.tex` · `part_B7.tex` · `rev4075_alias.tex`
- `rv4061_cellset.tex` · `rv4061_cuporder.tex` · `rv4061_ex_canonical-channel.tex` · `rv4061_ketptrace.tex` · `t2_fusion.tex` · `t2_lassodef.tex` · `t2_lassodef_v2.tex` · `t2_pentagon5.tex`
- `t2_staircase.tex` · `t2_twoshift.tex` · `tree_test.tex`

### Redraw fixtures (200)

- `adv_brace.tex` · `adv_conj.tex` · `adv_envs.tex` · `adv_leak.tex` · `adv_nested.tex` · `atoms_test.tex` · `audit1.tex` · `audit2.tex`
- `audit_open.tex` · `boundary_test.tex` · `cd_edge.tex` · `cd_test.tex` · `chain.tex` · `cups_edge.tex` · `cups_test.tex` · `ease_test.tex`
- `feat.tex` · `fig21d_cubic.tex` · `fig21d_cubic_v2.tex` · `fig21d_expect.tex` · `fig21d_pepo.tex` · `free.tex` · `free_modes.tex` · `free_test.tex`
- `free_typed_joins_ex.tex` · `g06_stageA.tex` · `g06_stageC.tex` · `gallery.tex` · `gr_t1_fusion.tex` · `gr_t3_action.tex` · `gr_t4_lasso.tex` · `gr_t5_zipper.tex`
- `gr_t6_leftinv.tex` · `gr_t7_coset.tex` · `gr_t8_sum.tex` · `grid_test.tex` · `hard01_ortho.tex` · `hard01_v3.tex` · `hard02_ALdef.tex` · `hard03_rdm.tex`
- `hard03_v2.tex` · `hard03_v3.tex` · `hard04_eig.tex` · `hard04_v2.tex` · `hard04_v3.tex` · `hard05_OL.tex` · `hard05_v2.tex` · `hard05_v4.tex`
- `hard06_gauge2layer.tex` · `hard06_v2.tex` · `hard06_v3.tex` · `hard06_v4.tex` · `hard07_peps.tex` · `hard07_v2.tex` · `hard08_mpu.tex` · `hard08_v2.tex`
- `hard08_v3.tex` · `hard09_pull.tex` · `hard09_v2.tex` · `hard10_pta.tex` · `hard10_v2.tex` · `hard10_v3.tex` · `hard11_circuit.tex` · `hard12_v2.tex`
- `hard12_v3.tex` · `hard12_zcl.tex` · `lattice_test.tex` · `lpos_probe.tex` · `modes_test.tex` · `notch.tex` · `p3_bisect_b.tex` · `p3_bisect_c.tex`
- `p3_blocking.tex` · `p3_corner.tex` · `p3_eq08.tex` · `p3_eq09.tex` · `p3_eq10.tex` · `p3_eq12.tex` · `p3_eq32.tex` · `p3_eq3_fusion.tex`
- `p3_eq3_v2.tex` · `p3_eq4_ortho.tex` · `p3_eq4_v2.tex` · `p3_eq8_action.tex` · `p3_eq8_v2.tex` · `p3_erase.tex` · `p3_ghostket_probe.tex` · `p3_inverse.tex`
- `p3_inverse_identity.tex` · `p3_min1.tex` · `p3_min2.tex` · `p3_multibond.tex` · `p3_multibond2.tex` · `p3_probe_opmod.tex` · `p3_probe_opop2.tex` · `p3_probe_pitch2.tex`
- `p3_reduce.tex` · `p3_regions.tex` · `p3_slidecd.tex` · `p3_sliding.tex` · `p3_wineq.tex` · `p4067_baseline.tex` · `p4067_gridbase.tex` · `p4067_pentagon.tex`
- `p_arrowtn.tex` · `p_usagefree.tex` · `part_B4.tex` · `part_B8.tex` · `pentagon_corrected.tex` · `plane_mirror_probe.tex` · `plane_stress.tex` · `plane_sweep1.tex`
- `plane_sweep2.tex` · `plane_sweep2_v2.tex` · `plane_sweep3.tex` · `plane_test.tex` · `planes_keys_test.tex` · `probe.tex` · `regress_x_pbc.tex` · `rem.tex`
- `rev4075_sig.tex` · `rgn.tex` · `rmpfig2_test.tex` · `rv4061_ex_atoms-keys.tex` · `rv4061_ex_boundary-doctrine.tex` · `rv4061_ex_cups-channels.tex` · `rv4061_ex_grid-benchmarks.tex` · `rv4061_ex_grid-mpo-stress.tex`
- `rv4061_vertlabel.tex` · `rv4061_vertonly.tex` · `rv_probe.tex` · `sheets_a_role.tex` · `sheets_test.tex` · `sheets_warn_smoke.tex` · `smoke.tex` · `stress.tex`
- `t2_ared.tex` · `t2_ared_loop.tex` · `t2_blocking.tex` · `t2_braidpat1.tex` · `t2_condensanyon.tex` · `t2_czx.tex` · `t2_eigladder.tex` · `t2_eq50_pull.tex`
- `t2_eq54_ginj.tex` · `t2_finegrain.tex` · `t2_gs1d.tex` · `t2_gs2d.tex` · `t2_gs2d_lasso.tex` · `t2_hamil_gate.tex` · `t2_hamilcommu.tex` · `t2_idempotent.tex`
- `t2_isometry.tex` · `t2_lassoC.tex` · `t2_lhsrhs1.tex` · `t2_lhsrhs2.tex` · `t2_lhsrhs3.tex` · `t2_lhsrhs4.tex` · `t2_lhsrhs5.tex` · `t2_lhsrhs6.tex`
- `t2_mpo.tex` · `t2_mpublock.tex` · `t2_mpubrick.tex` · `t2_mpucond.tex` · `t2_mpuflow.tex` · `t2_mpusplit.tex` · `t2_olvert.tex` · `t2_pairs.tex`
- `t2_pentagon2.tex` · `t2_pentagon3.tex` · `t2_pentagon4.tex` · `t2_pepo5.tex` · `t2_peps.tex` · `t2_probe_pepoupdown.tex` · `t2_probe_sides.tex` · `t2_purifyO.tex`
- `t2_renorm13.tex` · `t2_rgfp4.tex` · `t2_rhoR.tex` · `t2_seljbraid.tex` · `t2_sptgh_box.tex` · `t2_sptintertwin.tex` · `t2_sptmpo_cross.tex` · `t2_sv17.tex`
- `t2_tands.tex` · `t2_tcdual.tex` · `t2_tcdual_v2.tex` · `t2_tcprimal.tex` · `t2_tcprimal_v2.tex` · `t2_triangle.tex` · `t2_wrap9a.tex` · `trace_probe.tex`
- `xyz_a_lattice.tex` · `xyz_a_planes.tex` · `xyz_test.tex` · `zz_edgeprobe.tex` · `zz_frame_rotation.tex` · `zz_renderslice.tex` · `zz_siteprobe.tex` · `zz_vertprune.tex`

The preserved list includes these eight non-consumers: `geom.tex`, `modes_dot_baseline.tex`, `p_pitch.tex`, `p_species.tex`, `plane_experiment.tex`, `zz_geomdag.tex`, `zz_geomframe.tex`, `zz_geomsupport.tex`.

### Fixture raw-count reconciliation

| Raw construct | Occurrences |
|---|---:|
| `tenkz` | 467 |
| `tenkzfree` | 62 |
| `tenkzlattice` | 106 |
| `tenkzcd` | 15 |
| `tenkzplanes` | 36 |
| `tnpic` | 31 |
| `tntree` | 53 |
| **Total** | **770** |

## Retired-pipeline guard

The retired TeX tensor-network directory contains zero tracked files. The
demolition checker passes over the complete tracked tree and reports zero
retired catalogue calls, paths, or pipeline entry points. This inventory
introduces no compatibility path and no implementation change.

Reproduce the guards with:

```sh
python3 scripts/check_tenkz_dispositions.py
python3 scripts/check_tenkz_demolition.py
```
