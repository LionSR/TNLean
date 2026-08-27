# Cyclic-window cross-term reduction: a verbatim restatement retired

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for one gap-bound reduction in the
parent-Hamiltonian martingale layer whose statement repeated its neighbour
character for character.

| Removed | Replacement |
|---|---|
| `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_ordered_cross_term` (`TNLean/MPS/ParentHamiltonian/Martingale/Reduction.lean`) | `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_ordered_cross_term` in the same file, twenty-two lines earlier, which carries the proof |

## What was checked

The two theorems had byte-identical hypothesis lists and conclusions: the same
tensor and window-length binders, the same `1 < L` hypothesis, the same ordered
cross-term hypothesis quantified over chain lengths, index pairs marked by
`cyclicWindowsOverlap`, and vectors, and the same conjunction of positivity of
the constant `1 / (4 * L)` with the norm lower bound on the orthogonal
complement of the transported ground space. The removed theorem's entire proof
was `exact` applied to the survivor with the hypothesis passed straight through.

The removed name had a single caller,
`parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound` in the same
file, which now names the survivor. Because the signatures agree, the rest of
that proof is untouched.

## Blueprint and paper-gap redirections

The blueprint carried the duplicate as its own lemma node,
`lem:parent_hamiltonian_cyclic_overlap_ordered_cross_term_gap` in
`blueprint/src/chapter/ch13_parent_hamiltonian_spectral_gap_martingale_cyclic_overlap.tex`,
whose statement and proof restated the surviving node
`lem:parent_hamiltonian_cyclic_window_ordered_cross_term_gap`. The node, its
proof environment, and the equation label it introduced are deleted, and its
references are handled as follows.

* The two `\uses` lists in the same chapter, on the sufficient-norm-compression
  lemma and on that lemma's proof, are repointed to the surviving label.
* The long `\uses` list at
  `blueprint/src/chapter/ch13_parent_hamiltonian_spectral_gap_martingale.tex`
  already named the surviving label immediately before the dead one, so the dead
  entry is dropped rather than repointed, which would have duplicated it.
* The narrative sentence in the same chapter that introduced the duplicate as
  stating "the same overlap-only formulation" is deleted, since repointing it two
  lines after a reference to the survivor would have made the sentence refer to
  itself.
* `docs/paper-gaps/cpgsv21_martingale_overlap.tex` lists the cyclic-window
  compression reductions by name; the dead name there is replaced by the
  survivor, keeping the list complete.

After these edits no occurrence of the removed name or the deleted label remains
in `TNLean`, `blueprint/src`, or `docs`.

## Verification

Root `lake build` completes successfully with the package lean options.
`check_forbidden_lean_tokens.py`, `check_reader_facing_prose.py`,
`check_numbered_lean_files.py`, `check_oversized_lean_files.py` and
`generate_import_aggregators.py --check` are clean, and `leanblueprint checkdecls`
resolves every remaining tag.
