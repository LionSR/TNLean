# MPDO `Fin.append` Mathlib shadow removal

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for two local restatements of Mathlib
tuple lemmas, together with two proof shortenings that keep their statements.

## Removed declarations

| Removed | Replacement |
|---|---|
| `append_zero_eq` (root namespace, `TNLean/MPS/MPDO/PureAreaLaw.lean`) | `Fin.append_right_nil` (Mathlib, `Mathlib/Data/Fin/Tuple/Basic.lean`) |
| `MPOTensor.append_empty` (`private`, `TNLean/MPS/MPDO/MutualInfoBridge.lean`) | `Fin.append_right_nil` (Mathlib, same file) |

Both stated that appending an empty right block is the left block precomposed
with the length cast — verbatim the content of `Fin.append_right_nil`, which
carries the right block's length as a hypothesis `n = 0` rather than fixing it
to the literal `Fin 0`. The two use sites were migrated: the simp-only call in
`blockReducedState_zero` now names the Mathlib lemma, and the `rw` chain in
`mutualInfoChain_eq_mutualInformation` uses the closed form
`Fin.append_right_nil _ _ rfl`.

## Proofs shortened, statements kept

`append_glue` (`TNLean/MPS/MPDO/MutualInfoMonotone.lean`) and the `private`
`append_sub_self` (`TNLean/MPS/MPDO/MutualInfoBridge.lean`) keep their
statements and call sites; only their bodies change, from explicit
`Fin.addCases` splits to one Mathlib rewrite each — `Fin.append_cast_right` and
`Fin.append_right_nil` respectively. `append_glue` now mirrors the shape of
`append_assoc_cast` in the same file. Its two uses sit mid-`rw`-chain inside
`window_block_entropy`, where inlining the Mathlib lemma would require
restructuring that chain, so the wrapper stays.

## What was checked

No blueprint `\lean{}` tag names any of the four declarations, and no
documentation outside Lean references them. A root `lake build` is clean with
the package lean options, including the unused-simp-argument linter.

## Net effect

About 28 lines removed across the three files.
