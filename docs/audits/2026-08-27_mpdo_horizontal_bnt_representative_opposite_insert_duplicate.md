# Duplicate representative-indexed first-site theorems in horizontal BNT (2026-08-27)

`TNLean/MPS/MPDO/HorizontalBNT.lean` carried two theorems that restate,
verbatim, results already owned by the modules it imports. Both were removed
under the repository-local pass-through exception of
`docs/project_conventions.md` §Style, so no transition declaration is left
behind. Each removed statement is alpha-identical to its survivor: the same
explicit binders in the same order, the same implicit binders, and the same
conclusion, with only the physical-operator variable renamed (`Q` against `P`)
and the representative index renamed (`j` against `k`).

## Removed declarations

| Removed | Replacement |
|---|---|
| `MPOTensor.representative_opposite_insert_eq_of_rotated_mpo_entries` (`TNLean/MPS/MPDO/HorizontalBNT.lean`) | `MPOTensor.basis_opposite_insert_eq_of_rotated_mpo_entries` in `TNLean/MPS/MPDO/HorizontalCFMPVRepresentation.lean`. The two statements agree on all seven explicit binders — the tensor, the sector decomposition, the canonical-form hypothesis, the positive-length matrix product vector agreement, the physical operator, and the two entrywise first-site identities — and on the conclusion that the two opposite-corner insertions agree on every minimal representative. At the audited head the removed name had no non-`Archive` Lean consumer. |
| `MPOTensor.representative_braRight_eq_ketLeftBraRight_of_invariant` (same file) | `MPOTensor.basis_braRight_eq_ketLeftBraRight_of_invariant` in `TNLean/MPS/MPDO/InvariantProjection.lean`. The two statements agree in binder kind and order, and the proof bodies were textually the same appeal to the canonical form together with the invariant-projection first-site agreement. Its two consumers inside `HorizontalBNT.lean`, `MPOTensor.IsHorizontalCF.exists_representative_braRight_eq_ketLeftBraRight` and `MPOTensor.IsHorizontalCF.braRight_eq_ketLeftBraRight_of_invariant`, now call the survivor with an unchanged argument list; `HorizontalBNT.lean` already imports `TNLean.MPS.MPDO.InvariantProjection`, so no import changed. |

## Blueprint

The composite node `thm:representative_one_sub_mp_zero`
(`blueprint/src/chapter/ch20_mpdo_canonical_forms_first_site_contractions.tex`)
named both removed declarations. Its `\leanok` and every other payload stay,
and no prose was edited.

* The opposite-corner payload was **repointed** to
  `MPOTensor.basis_opposite_insert_eq_of_rotated_mpo_entries` rather than
  deleted. The node's statement asserts that the specialized identity follows
  from the two entrywise identities at every positive length, which is exactly
  the claim of the removed theorem; repointing keeps that clause witnessed in
  Lean under the node's `\leanok`. The survivor is also the payload of
  `thm:blockwise_opposite_insert_rotated_mpo`, which is left untouched;
  payloads shared between nodes already occur throughout this blueprint.
* The invariant-projection payload was **deleted** rather than repointed. Its
  survivor, `MPOTensor.basis_braRight_eq_ketLeftBraRight_of_invariant`, is
  already the sole payload of `thm:blockwise_one_sub_mp_zero`, and the
  representative-level claim in the body of
  `thm:representative_one_sub_mp_zero` stays witnessed by the retained payload
  `MPOTensor.IsHorizontalCF.exists_representative_braRight_eq_ketLeftBraRight`.

`blueprint/lean_decls` was regenerated with
`scripts/blueprint_lean_sync.py --root . --update-lean-decls`; it lost both
removed names and retains both survivors.
