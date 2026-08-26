# QCA simplification sweep, 2026-08-26

This note records a three-part deletion in the `QCA/` layer. Every removed
declaration is a pass-through, a zero-consumer restatement, or a member of a
retired parallel predicate family, so no deprecation alias is introduced
(`docs/project_conventions.md` §Style). Each removal is listed below with its
replacement.

## 1. The one-sided tensor-submodule twin in the bipartite support algebra

`TNLean/QCA/BipartiteSupportAlgebra.lean` carried a `Fin`-restricted left
statement phrased through QICLean's `Matrix.tensorSubmodule`, plus a bridge
identifying that submodule with the local Kronecker span at an unrestricted
right factor. The Kronecker span is the module's own construction and is not
restricted to `Fin` index types, so the left statement is now proved directly
against it, mirroring the surviving right statement line for line.

| Removed | Replacement |
|---|---|
| `Matrix.left_support_algebra_le_iff_le_tensor_submodule` | `Matrix.left_support_algebra_le_iff_le_kronecker_submodule` — same content with the `Fin` restriction dropped |
| `Matrix.kroneckerSubmodule_top_eq_tensorSubmodule` | `Matrix.mem_kroneckerSubmodule_iff` at right factor `⊤` |

Consequences:

- The blueprint node `thm:qca_left_support_tensor_submodule` keeps its label
  and is restated against the Kronecker span; its `\lean{}` tag now points at
  the surviving theorem. It was moved after `def:qca_kronecker_submodule` so
  its `\uses` is no longer a forward reference.
- The blueprint node `thm:qca_kronecker_submodule_top` is deleted. It was
  terminal: nothing cited it.
- `docs/paper-gaps/gnvw12_support_algebra_full_matrix_scope.tex` had its
  `\leanid` migrated to the surviving name. The recorded gap is unchanged:
  the restriction is to full matrix factors rather than arbitrary
  finite-dimensional C*-algebra factors, and removing the `Fin` binders does
  not close it. The module's `**Scope restriction (full matrix factors):**`
  marker stays as written.
- The module no longer needs `QICLean.Channel.OperatorSystem`. It imports
  `QICLean.Channel.TensorMap` for `Matrix.bipartiteSlice` and
  `Mathlib.LinearAlgebra.Dimension.Free` for `Module.finBasis`, both of which
  had been arriving transitively.

## 2. Zero-consumer finite-region arithmetic and point-free composition twins

Seven declarations had no consumer anywhere outside `Archive/` and their own
defining lines. Each restates a Mathlib fact under a project name, or gives a
point-free form of a pointwise lemma that is itself retained.

| Removed | Replacement |
|---|---|
| `SpinChain.regionSumset_empty_left` | `Finset.empty_add` |
| `SpinChain.regionSumset_empty_right` | `Finset.add_empty` |
| `SpinChain.regionSumset_translateRegion_left` | `SpinChain.regionSumset_assoc` with `SpinChain.regionSumset_singleton_right` |
| `SpinChain.regionSumset_translateRegion_right` | `SpinChain.regionSumset_assoc` with `SpinChain.regionSumset_singleton_right` |
| `SpinChain.translateRegion_injective` | `Finset.map_injective` |
| `SpinChain.localTranslation_comp_localInclusion` | `SpinChain.localTranslation_localInclusion` (the pointwise form) |
| `SpinChain.algebraicLocalUnblockingHom_comp_blockingHom` | `SpinChain.algebraicLocalBlocking` (the equivalence carries both directions) |

Retained on purpose: `SpinChain.siteTranslation_add` and
`SpinChain.Config.translation_add`, which state the group law for the site and
configuration translations rather than region arithmetic;
`SpinChain.regionSumset_zero_left`, `SpinChain.regionSumset_zero_right`, and
`SpinChain.regionSumset_assoc`, which are simp lemmas or carry live consumers;
`SpinChain.algebraicLocalBlockingHom_comp_unblockingHom`, which is used in the
construction of the blocking equivalence.

The blueprint nodes `def:qca_translate_region`, `def:qca_region_sumset`,
`lem:qca_finite_local_translation_naturality`, and
`lem:qca_algebraic_blocking_maps_evaluation` lost the corresponding `\lean{}`
entries, and their prose lost the sentences and display rows asserting the
removed facts. No label was deleted and no `\uses` needed repointing.

## 3. The two-sided finite-propagation predicate family

`TNLean/QCA/TwoSidedPropagation.lean` and a section of
`TNLean/QCA/FinitePropagation.lean` maintained a second propagation predicate
family alongside the forward-only one that the sources actually define
(arXiv:1703.09188, Appendix, line 2298; Schumacher--Werner, quant-ph/0405174,
Definition 1). The family was self-contained: every member was cited only by
another member or by one of three blueprint nodes covering the same family. The
whole module and its section are removed.

| Removed | Replacement |
|---|---|
| `SpinChain.PropagatesWithinTwoSided` | `SpinChain.PropagatesWithin` applied to `ω` and to `ω.symm` |
| `SpinChain.HasTwoSidedFinitePropagation` | `SpinChain.HasFinitePropagation` applied to `ω` and to `ω.symm` |
| `SpinChain.PropagatesWithinTwoSided.mono` | `SpinChain.PropagatesWithin.mono` on each side |
| `SpinChain.PropagatesWithinTwoSided.of_reflected` | `SpinChain.PropagatesWithin.mono` on each side |
| `SpinChain.PropagatesWithinTwoSided.exists_symmetric_Icc` | `SpinChain.PropagatesWithin.exists_symmetric_Icc` on each side |
| `SpinChain.PropagatesWithinTwoSided.of_forward` | `SpinChain.PropagatesWithin.symm` with `SpinChain.PropagatesWithin.mono` |
| `SpinChain.HasTwoSidedFinitePropagation.exists_common_neighborhood` | `SpinChain.HasFinitePropagation.exists_superset` |
| `SpinChain.HasTwoSidedFinitePropagation.exists_symmetric_Icc` | `SpinChain.HasFinitePropagation.exists_symmetric_Icc` on each side |
| `SpinChain.hasFinitePropagation_iff_hasTwoSidedFinitePropagation` | `SpinChain.HasFinitePropagation.symm` |
| `SpinChain.HasFinitePropagation.exists_common_twoSided_neighborhood` | `SpinChain.HasFinitePropagation.symm` with `SpinChain.HasFinitePropagation.exists_superset` |
| `SpinChain.HasFinitePropagation.exists_twoSided_symmetric_Icc` | `SpinChain.HasFinitePropagation.symm` with `SpinChain.HasFinitePropagation.exists_symmetric_Icc` |
| `SpinChain.neg_symmetric_Icc` | no consumer; `Finset.Icc (-(R : ℤ)) (R : ℤ)` under reflection appears nowhere else outside `Archive/` |

Retained on purpose, because they carry the forward-only content the sources
state and have live consumers: `SpinChain.PropagatesWithin.symm`,
`SpinChain.HasFinitePropagation.symm`,
`SpinChain.exists_subset_symmetric_Icc` (called by
`SpinChain.PropagatesWithin.exists_symmetric_Icc`),
`SpinChain.PropagatesWithin.exists_symmetric_Icc`, and
`SpinChain.HasFinitePropagation.exists_symmetric_Icc`.

Three blueprint nodes are deleted with the family:
`def:qca_two_sided_finite_propagation`,
`lem:qca_two_sided_common_neighborhood`, and
`thm:qca_forward_iff_two_sided_propagation`. Each was cited only from inside
the other two, so no `\uses` needed repointing.
`lem:qca_finite_propagation_symmetric_interval` and
`lem:qca_propagation_neighborhood_mono` survive untouched.

`TNLean/QCA.lean` was regenerated with
`python3 scripts/generate_import_aggregators.py`.

## Checks

- `lake build` completes successfully with the package lean options; no new
  warning on any touched file.
- `rg -n "sorry|axiom"` is clean on every touched Lean file.
- `python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls` reports
  the blueprint and Lean code in sync, and `lake exe checkdecls
  blueprint/lean_decls` exits zero.
