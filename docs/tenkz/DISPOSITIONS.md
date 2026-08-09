# tenkz migration dispositions

This inventory is the migration ledger for issue #4748. It classifies the
tracked tree on the PR's current base against the signed 1.0 contract in
`LANGUAGE-1.0.md` §§9–12. The
classification concerns the S4 surface switch, not whether a figure is
mathematically or visually correct today. The committed disposition checker
keeps the line inventory, fixture lists, and reconciliation tables synchronized
with the tracked TeX sources.

## Disposition rules

- **Preserve** means a pure `tenkz` grid construct already uses kernel
  vocabulary. It remains byte-compatible at the surface switch. A key with a
  signed `kernel-` registry row counts as kernel vocabulary whether its status
  is `kernel` or `sugar(...)`, because a sugar row carries no sunset: the
  switch leaves it spelled exactly as it stands. This holds only under the
  kernel switch, which is where a key already means what 1.0 says it means.
- **Codemod** means every non-kernel spelling has a mechanical expansion in
  the §9 sugar ledger or an exact 0.7 atom-shorthand respelling to 1.0 atom
  keys. The target codes below name that expansion. The same key on a 0.7
  picture is a non-kernel spelling even when the kernel carries a row of that
  name, because the two tiers read several of them differently: 0.7
  `boundary=` sets all four sides where the kernel sets west and east, and
  0.7 `physical=` is a row topology where the kernel's is a per-cell port
  policy.
- **Redraw** means the construct depends on a §10 tombstone. Its mathematical
  boundary and topology must be re-authored with the named §12-style shape;
  a compatibility-renderer transcription is not a migration.
- A fixture receives its most demanding disposition: redraw outranks codemod,
  which outranks preserve. Classification follows local `\input`/`\include`
  dependencies and setup commands, not only picture constructs in the
  top-level file.

### Migration target codes

| Code | Required 1.0 target |
|---|---|
| `P-grid` | Keep the existing pure-kernel `tenkz` or `tenkzeq` spelling byte-compatible. |
| `P-none` | Keep the fixture; it has no tenkz public-surface construct. |
| `C-declare` | Replace compatibility setup lists with `\tndeclare` records. |
| `C-picture` | Expand `\tnpic` to a scoped `tenkz` picture term. |
| `C-tree` | Expand `\tntree` to declared fuse atoms and `\tnwire` records. |
| `C-policy` | Expand 0.7 physical/boundary sugar and the boundary-label keys to `rows=`, typed `ports=`, and explicit side policies. |
| `C-frame` | Expand lattice/ring/surface/planes/cluster sugar to rows, columns, frame, basis members, and explicit closures. |
| `C-record` | Expand atom, wire, span, skip, and port sugar; respell 0.7 atom flags as `skin=` and typed `ports=` on `\tn`, `\tnwire`, and `\tnmark` records. |
| `C-species` | Replace `role=` with the corresponding declared `species=`. |
| `C-switch` | Remove the temporary `\tenkzkernel` opt-in when the kernel becomes the public surface at S4. |
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
| `ch02_mps.tex` | L25, 56, 176, 208, 281, 851, 981 `tenkz` → `P-grid` | — | — |
| `ch03_single.tex` | L251 `tenkz` → `P-grid` | — | — |
| `ch04_channels_choi_foundations.tex` | L87 `tenkz` → `P-grid` | — | — |
| `ch11_fundamental_theorem_core.tex` | L42, 46 `tenkz` → `P-grid` | — | — |
| `ch12_symmetry_string_order.tex` | L41, 80, 362, 367, 398, 404, 449, 455, 488, 493, 531, 537, 842, 847 `tenkz` → `P-grid` | — | — |
| `ch12_symmetry_virtual_and_cohomology.tex` | L181, 196, 330, 459, 473 `tenkz` → `P-grid` | — | — |
| `ch13_parent_hamiltonian_commuting_gap_appendix_b_commutation.tex` | L55 `tenkz` → `P-grid` | — | — |
| `ch13_parent_hamiltonian_commuting_gap_appendix_b_supports.tex` | L276 `tenkz` → `P-grid` | — | — |
| `ch13_parent_hamiltonian_injective_ground_spaces_intersection_property.tex` | L101 `tenkz` → `P-grid` | — | — |
| `ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex` | L36, 994, 1036 `tenkz` → `P-grid` | — | — |
| `ch14_correlations.tex` | L68 `tenkz` → `P-grid` | — | — |
| `ch16_channel_representations_choi_and_kraus.tex` | L691 `tenkz` → `P-grid` | — | — |
| `ch16_channel_representations_dilations_and_ordered_cp.tex` | L23 `tenkz` → `P-grid` | — | — |
| `ch20_mpdo_canonical_forms_first_site_contractions.tex` | L154, 161, 181, 186, 234, 240, 339, 433 `tenkz` → `P-grid` | — | — |
| `ch20_mpdo_canonical_forms_intro_finite_separation.tex` | L105, 109, 221, 229, 368, 381, 432 `tenkz` → `P-grid` | — | — |
| `ch20_mpdo_canonical_forms_positivity_gram_normalization.tex` | L638, 644 `tenkz` → `P-grid` | — | — |
| `ch20_mpdo_foundations.tex` | L17, 126, 373, 377 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_algebra_tower.tex` | L79, 95 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_blocked_rfp_positive_blocking_and_sector_algebra.tex` | L19, 24 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_foundations.tex` | L87, 92 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_fusion_isometries_complete_zipper_coherence.tex` | — | L215, 219, 293, 294, 295, 296, 298 `tntree` → `C-tree` | — |
| `ch21_mpdo_rfp_fusion_isometries_fixed_final_comparison.tex` | — | L572, 577 `tntree` → `C-tree` | — |
| `ch21_mpdo_rfp_fusion_isometries_foundations.tex` | L403, 413, 648, 657, 669, 678, 690, 695 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_fusion_isometries_product_laws.tex` | L45, 61, 65, 465 `tenkz` → `P-grid` | L577, 579 `tntree` → `C-tree` | — |
| `ch21_mpdo_rfp_renormalization.tex` | L632, 635, 638, 641 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_simple_local_closed_sector_contractions.tex` | L282, 288 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_simple_local_inverse_map_factorization.tex` | L44, 49, 53, 70, 78, 130, 265, 270, 275, 282, 287, 486, 704, 710, 714 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_simple_local_neighboring_bond_contractions.tex` | L793, 806, 814, 821, 895, 902 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_simple_local_primitivity_active_trace_matrix.tex` | L189 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_simple_local_refinement_channels_physical_coordinates.tex` | L326, 332, 338, 352, 363, 369 `tenkz` → `P-grid` | — | — |
| `ch21_mpdo_rfp_simple_local_structure_capstone.tex` | L363, 882, 886, 892, 897 `tenkz` → `P-grid` | — | — |
| `ch23_algebraic_ft_foundations.tex` | L48, 52, 169, 173, 374, 378, 391, 395, 438, 442, 446, 455, 459 `tenkz` → `P-grid` | — | — |
| `ch24_peps_ft.tex` | L27, 57, 93 `tenkz` → `P-grid` | — | — |
| `ch24_peps_ft_balanced_edge_scalars.tex` | L21 `tenkz` → `P-grid` | — | — |
| `ch24_peps_ft_edge_kernel_gauges_absorption_scalar_comparison.tex` | L84, 104, 294, 300, 312, 324, 577, 596 `tenkz` → `P-grid` | — | — |
| `ch24_peps_ft_edge_kernel_gauges_insertion_algebra_local_gauges.tex` | L53, 60 `tenkz` → `P-grid` | — | — |
| `ch24_peps_ft_edge_kernel_gauges_kernel_descent_recovery.tex` | L175, 180, 187, 400, 407, 414 `tenkz` → `P-grid` | — | — |
| `ch24_peps_ft_edge_middle.tex` | L273 `tenkz` → `P-grid` | — | L246 `tenkz` → `R-record` |
| `ch24_peps_ft_foundations.tex` | L49, 377 `tenkz` → `P-grid` | — | — |
| `ch24_peps_ft_normal_capstone_normal_peps.tex` | — | — | L45, 92, 108 `tenkz` → `R-record` |
| `ch24_peps_ft_normal_square_blocking_and_fundamental.tex` | L193, 199 `tenkz` → `P-grid` | — | L21, 28, 89, 95, 115, 151, 163 `tenkz` → `R-record` |
| `ch24_peps_ft_normal_square_coordinate_regions.tex` | — | — | L100, 106, 126, 293 `tenkz` → `R-record` |
| `ch24_peps_ft_normal_square_rectangular_injectivity.tex` | — | — | L206, 229 `tenkz` → `R-record` |
| `ch24_peps_ft_normal_square_translated_windows_and_comparison.tex` | — | — | L382 `tenkz` → `R-record` |
| `ch24_peps_ft_normal_union.tex` | L214, 263, 289, 301, 316 `tenkz` → `P-grid` | — | — |
| `ch24_peps_ft_region_transfer_covariance.tex` | L351, 355, 359, 363 `tenkz` → `P-grid` | — | — |
| `ch24_peps_ft_torus_translation_and_reference_windows.tex` | L23 `tenkz` → `P-grid` | — | — |
| `ch26_mps_rfp_normal_isometry_canonical_forms.tex` | L453, 457, 606, 612 `tenkz` → `P-grid` | — | — |
| `ch26_mps_rfp_physical_blocking.tex` | L198, 202, 220, 225 `tenkz` → `P-grid` | — | — |

### Blueprint reconciliation

| Raw construct | Occurrences |
|---|---:|
| `tenkz` | 191 |
| `tenkzcd` | 0 |
| `tenkzplanes` | 0 |
| `tnpic` | 0 |
| `tntree` | 11 |
| **Total** | **202** |

| Disposition | Occurrences |
|---|---:|
| preserve | 173 |
| codemod | 11 |
| redraw | 18 |
| **Total** | **202** |

The raw count is 191 environment openings plus 11 command occurrences,
which reconciles to 202. The issue baseline counted 106 `tenkz`,
36 `tenkzfree`, 18 `tenkzlattice`, 6 `tenkzcd`, 0 `tenkzeq`,
0 `tenkzplanes`, and 41 `\tnpic`/`\tntree` lines; the six `tenkzcd`
pictures have since been respelled onto plain tikz-cd, discharging every
blueprint `R-cd` row, and the twenty `\tnpic` pictures have since been
redrawn as kernel grid pictures, discharging every blueprint `\tnpic` row.

## Standalone fixture inventory

The source root for every file below is `tests/tenkz/`. The S4 surface swap
has executed: the grid front end is deleted, the kernel is the package
surface, and every fixture whose disposition was codemod or redraw has left
the corpus, its behaviours dying with the dialect or covered by the kernel
and RMP suites per `FIXTURE-RETIREMENT.md`. What remains is the surviving
corpus itself.

| Disposition | Fixtures |
|---|---:|
| preserve | 9 |
| **Total** | **9** |

Of the 9 top-level fixtures, 5 open the (kernel) tenkz environment and 4
contain no tenkz public-surface construct.

### Preserve fixtures (9)

- `P-grid`: `fig21d_cubic.tex` · `fig21d_cubic_v2.tex` · `iso_h.tex` · `p3_probe_opop.tex` · `rv4061_flatonly.tex`
- `P-none`: `plane_experiment.tex` · `zz_geomdag.tex` · `zz_geomframe.tex` · `zz_geomsupport.tex`

Three corrections executed with the swap, against the pre-swap ledger:

- `trace_warn.tex` and `zz_wirescan.tex` were classified preserve, but each
  pinned a grid-only property: the one a grid misuse warning
  (`grid-interface-range`), the other the grid boundary pass's virtual
  pairing and a model lookup whose only caller was the grid walk. Both died
  with the front end.
- The `C-switch` code executed: `fig21d_cubic.tex` and `fig21d_cubic_v2.tex`
  dropped their `\tenkzkernel` opt-in lines, which the load-time surface
  makes redundant.
- The three preserves that omitted a column count (`iso_h.tex`,
  `p3_probe_opop.tex`, `rv4061_flatonly.tex`) now spell `cols=` explicitly:
  the 0.7 grid sized its columns from the body, while the kernel frame's
  `cols=` defaults to 3 and populates, so the omitted key was the one
  spelling whose meaning the switch changed.

### Fixture raw-count reconciliation

| Raw construct | Occurrences |
|---|---:|
| `tenkz` | 5 |
| `tenkzeq` | 0 |
| `tnpic` | 0 |
| `tntree` | 0 |
| **Total** | **5** |

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
