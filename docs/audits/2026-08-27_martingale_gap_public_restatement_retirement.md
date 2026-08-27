# Martingale gap-bound public restatements retired

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for four gap-bound theorems in
`TNLean/MPS/ParentHamiltonian/Martingale/Gap.lean` that restated, character for
character, theorems already carried by
`TNLean/MPS/ParentHamiltonian/Martingale/Reduction.lean`.

| Removed | Replacement |
|---|---|
| `MPSTensor.parentHamiltonianES_gap_bound_of_anticommutator` (`Martingale/Gap.lean`) | `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_anticommutator` (`Martingale/Reduction.lean`) |
| `MPSTensor.parentHamiltonianES_gap_bound_of_overlap_norm_constant` (`Martingale/Gap.lean`) | `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_lt` (`Martingale/Reduction.lean`) |
| `MPSTensor.parentHamiltonianES_gap_bound_of_overlap_norm_bound` (`Martingale/Gap.lean`) | `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound` (`Martingale/Reduction.lean`) |
| `MPSTensor.parentHamiltonianES_gap_bound_of_overlap_operator_norm_constant` (`Martingale/Gap.lean`) | `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_operator_norm_of_lt` (`Martingale/Reduction.lean`) |

## What was checked

Each removed theorem had the hypothesis list and conclusion of its replacement
verbatim: the same tensor and window-length binders, the same `1 < L`
hypothesis, the same all-vector estimate quantified over chain lengths and over
off-diagonal index pairs marked by `cyclicWindowsOverlap`, and the same
conjunction of positivity of the gap constant with the norm lower bound on the
orthogonal complement of the transported ground space.

Three of the four had a proof consisting of `exact` applied to the replacement
with every argument passed straight through. The fourth,
`parentHamiltonianES_gap_bound_of_overlap_norm_bound`, was a byte-identical
statement re-proved by a second route: it instantiated the constant-flexible
theorem at `η = (1 - 1/(4L)) / (2(L-1))` and rewrote the resulting coefficient
back to `1/(4L)`. The replacement in `Reduction.lean` proves the same statement
directly from the cyclic-window ordered cross-term reduction, so the arithmetic
detour carried no additional content.

Five call sites were involved. Four are the surviving public spectral-gap
theorems in the same file — `parentHamiltonian_gapped`,
`parentHamiltonian_gapped_of_anticommutator`,
`parentHamiltonian_gapped_of_overlap_norm_constant` and
`parentHamiltonian_gapped_of_overlap_operator_norm_constant` — each of which now
names the `Reduction.lean` theorem directly; because the signatures agree, the
argument lists are unchanged and only one call needed re-wrapping to stay inside
the column limit. The fifth call site was the invocation of
`parentHamiltonianES_gap_bound_of_overlap_norm_constant` inside the deleted
proof of `parentHamiltonianES_gap_bound_of_overlap_norm_bound`; it disappeared
with the block.

No module outside `Martingale/` referenced any of the four removed names.
`TNLean/MPS/ParentHamiltonian/Martingale/BlockedGap.lean` consumes
`parentHamiltonianES_gap_bound_of_cyclic_window_overlap_anticommutator`
directly, which is independent evidence that the `Reduction.lean` copies are the
live ones. Three docstrings that named a removed theorem — the module docstring
and the `parentHamiltonian_gapped` docstring in `Gap.lean`, the reduction
docstring in `Reduction.lean`, and the spectral-theorem docstring in
`AbstractCriterion.lean` — were repointed to the corresponding survivor.

## Blueprint and paper-gap redirections

The blueprint carries four theorem nodes for these statements in
`blueprint/src/chapter/ch13_parent_hamiltonian_spectral_gap_martingale.tex`:
`thm:overlap_norm_gap_bound`, `thm:anticommutator_gap_bound`,
`thm:overlap_norm_gap_bound_constant` and
`thm:overlap_operator_norm_gap_bound_constant`. The nodes are kept and their
`\lean{...}` payloads repointed to the surviving declarations, rather than
deleted: between them they carry two, four, four and three inbound edges from
other nodes in the chapter, and deleting them would have severed those edges
without simplifying the mathematics. Every `\label`, `\uses`, `\ref` and
`\leanok`, and every theorem statement body, is untouched.

Each of the four proof environments previously described its node as a
restatement of a separate declaration, and each of those `\uses` lists now names
the label carrying the node's own payload. The prose is rewritten to state the
mathematical content directly — the finite-overlap martingale reduction with the
cyclic overlap relation, the constant-`η` compression reduction, and the
symmetric anticommutator conversion of the operator-product bound — so that no
sentence claims the node restates a distinct declaration.

`docs/paper-gaps/cpgsv21_martingale_overlap.tex` named three of the removed
declarations in footnote inventories and one in its blueprint-relation section.
In each footnote the surviving declaration was already listed one or two lines
above, so the removed entry is dropped rather than repointed, which would have
duplicated the neighbouring entry; the surrounding sentence is rewritten to name
the single surviving statement. The blueprint-relation paragraph now describes
`thm:anticommutator_gap_bound`, `thm:overlap_norm_gap_bound` and
`thm:overlap_norm_gap_bound_constant` as pointing to the cyclic-window
reductions in `TNLean/MPS/ParentHamiltonian/Martingale/Reduction.lean`, and no
sentence describes a two-layer entry-point-versus-public-reformulation split for
these four, since that split is what the change removes.

After these edits no occurrence of any removed name remains in `TNLean`,
`blueprint/src`, `docs` or `scripts`.

## Verification

Root `lake build` completes successfully with the package lean options.
`check_forbidden_lean_tokens.py`, `check_reader_facing_prose.py`,
`check_numbered_lean_files.py`, `check_oversized_lean_files.py` and
`generate_import_aggregators.py --check` are clean, and `checkdecls` against a
regenerated `blueprint/lean_decls` resolves every remaining tag.
