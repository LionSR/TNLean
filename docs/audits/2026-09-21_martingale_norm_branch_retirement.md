# Retirement of the conditional norm-compression martingale branch

This audit records the deletion of the norm-compression and operator-norm
branch of the conditional martingale gap ladder from
`TNLean/MPS/ParentHamiltonian/Martingale/Gap.lean` and
`TNLean/MPS/ParentHamiltonian/Martingale/Reduction.lean`, together with the
blueprint nodes that stated it. It is the audit note required by
`docs/project_conventions.md` §Style. No compatibility alias is provided for
any removed declaration.

## What was superseded

The removed theorems derived a uniform spectral gap for the MPS parent
Hamiltonian from an all-vector excitation-projection compression estimate
`‖pᵢ(pⱼv)‖ ≤ η‖pᵢv‖`, or from the symmetric operator-product estimate
`‖pᵢ(pⱼv)‖ ≤ η‖pⱼv‖`, on overlapping cyclic windows. Both are stronger than
the source anticommutator condition of arXiv:2011.12127 §IV.C
(`TN-Review-main.tex:2176-2180`). The directional form forces
`pⱼ(ker pᵢ) ⊆ ker pᵢ`, and the operator-product form is unsatisfiable for
`η < 1` whenever the overlapping excitation ranges share a nonzero vector,
since then `‖pᵢpⱼ‖ = 1`. The paper-gap note
`docs/paper-gaps/cpgsv21_martingale_overlap.tex` documented both as
conditional non-source reductions and asked for their replacement; the
unconditional blocked range-two capstone has since landed, and no discharger
for the all-vector estimate exists anywhere in the development.

## Removed declarations and their replacements

* `MPSTensor.parentHamiltonian_gapped`, the public gap statement under the
  norm-compression hypothesis, replaced by
  `MPSTensor.parentHamiltonian_gapped_of_anticommutator`.
* `MPSTensor.parentHamiltonian_gapped_of_overlap_norm_constant`, replaced by
  `MPSTensor.parentHamiltonian_gapped_of_anticommutator`.
* `MPSTensor.parentHamiltonian_gapped_of_overlap_operator_norm_constant`,
  replaced by `MPSTensor.parentHamiltonian_gapped_of_anticommutator`.
* `MPSTensor.parentHamiltonianES_quadratic_form_of_finite_overlap_norm_bound`
  and `..._of_le`, with no replacement; the anticommutator finite-overlap
  reduction `MPSTensor.parentHamiltonianES_quadratic_form_of_finite_overlap_anticommutator`
  is the retained route.
* `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound`,
  `..._of_le`, and `..._of_lt`, replaced by
  `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_anticommutator`.
* `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_operator_norm_of_le`
  and `..._of_lt`, replaced by
  `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_anticommutator`.

All ten had zero consumers outside the removed branch. The all-vector
estimate hypothesis occurred outside `Gap.lean`/`Reduction.lean` only as an
exact identity in `Transport.lean`, never as a discharged instance.

## Blueprint nodes removed

Nine nodes were deleted: `thm:overlap_norm_gap_bound`,
`thm:overlap_norm_gap_bound_constant`,
`thm:overlap_operator_norm_gap_bound_constant`,
`thm:parent_hamiltonian_gapped_constant`,
`thm:parent_hamiltonian_gapped_operator_norm_constant` from
`blueprint/src/chapter/ch13_parent_hamiltonian_spectral_gap_martingale.tex`,
and `lem:parent_hamiltonian_finite_overlap_norm_quadratic`,
`lem:parent_hamiltonian_cyclic_overlap_norm_gap`,
`lem:parent_hamiltonian_cyclic_overlap_norm_constant_gap`,
`lem:parent_hamiltonian_cyclic_overlap_operator_norm_constant_gap` from
`blueprint/src/chapter/ch13_parent_hamiltonian_spectral_gap_martingale_cyclic_overlap.tex`.
The tracking list named eight nodes; the ninth,
`lem:parent_hamiltonian_cyclic_overlap_norm_gap`, was a duplicate tag on
`MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound`
(recorded in `docs/audits/2026-09-19_blueprint_duplicate_declaration_tags.md`)
and had to be deleted with its declaration.

`thm:parent_hamiltonian_gapped` was trimmed, not deleted: it lost the
`\lean{MPSTensor.parentHamiltonian_gapped}` payload and the
"or the stronger norm-compression estimate" clause, and now states the
anticommutator hypothesis alone under
`\lean{MPSTensor.parentHamiltonian_gapped_of_anticommutator}`. Every
`\uses`/`\ref` edge that pointed at a removed node was removed with it;
`thm:anticommutator_gap_bound` and `thm:martingale_criterion` are unchanged.

### Blueprint-owner sign-off

Per the requirement in #7857, repository and blueprint owner Sirui Lu
(@LionSR) signed off on deleting the eight named blueprint nodes (and the
duplicate `lem:parent_hamiltonian_cyclic_overlap_norm_gap`) outright rather than
redirecting them to a normal/primitive capstone, because the norm-compression
and operator-norm hypotheses are non-source and unsatisfiable when overlapping
excitation ranges intersect.

## What was checked

* Linter-bearing builds of `TNLean.MPS.ParentHamiltonian.Martingale.Gap`,
  `...Reduction`, `...AbstractCriterion`, and `...BlockedGap`, then a root
  build of `TNLean.MPS.ParentHamiltonian` — all clean.
* Grep over `TNLean/` and `blueprint/src/` for each removed declaration name
  and each removed node label: zero remaining references.
* `scripts/blueprint_lean_sync.py --update-lean-decls` and `--ci`: in sync.
* `scripts/generate_import_aggregators.py --check`: current; the surviving
  short `Gap.lean` keeps the Martingale aggregator unchanged.
* `docs/paper-gaps/cpgsv21_martingale_overlap.tex` compiles standalone; its
  restated sections now describe the removed branch in the past tense and
  reference the removed declarations with `\path`, not `\leanid`.
* The docstrings at `AbstractCriterion.lean` (module header and
  `spectralGap_of_martingale_of_finiteDimensional`) now name the
  anticommutator theorem as the MPS-specific instance.

## What is retained and why

The whole anticommutator chain stays: `parentHamiltonian_gapped_of_anticommutator`,
`parentHamiltonianES_gap_bound_of_cyclic_window_overlap_anticommutator`, the
finite-overlap anticommutator reductions, `thm:martingale_criterion`, and
every anticommutator blueprint node. The QICLean projection-geometry
norm-compression lemmas
(`ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_norm_bound`
and companions) lose their last TNLean consumer here but live in the QICLean
dependency and are out of this PR's scope; their blueprint node in
`ch13_parent_hamiltonian_spectral_gap_hilbert_space_rowsum.tex` is untouched.

## Cross-references and deferred work

The deletion follows the superseded-route precedent S7 of
`docs/proof_debt_ledger.md`. The remaining live gap work — a finite-volume
estimate on the short periodic chains `2(l+1) ≤ N < 2m` left open by the
finite-range Knabe capstone — is tracked separately in #7742 and is
unaffected: the removed branch never supplied it. Nothing is deferred from
this removal.
