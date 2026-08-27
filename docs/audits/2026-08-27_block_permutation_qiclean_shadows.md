# Block-permutation shadows, a repeated state-vector expansion, and a private scaling clone

This audit records three cross-cutting removals in one change, all covered by
the repository-local pass-through exception of `docs/project_conventions.md`
§Style. No `@[deprecated] alias` is retained: every non-`Archive` use of every
removed name is migrated in the same change, and none of the removed names
encodes misleading terminology.

| Removed | Replacement |
|---|---|
| `MPSTensor.ringEquiv_maps_single_support` (`TNLean/MPS/Structure/BlockPermutation.lean`) | `TwoSidedIdeal.ringEquiv_maps_single_support_between` (`QICLean/Algebra/BlockPermutation.lean`) |
| `MPSTensor.componentMapRingHom` (private, same file) | none needed: its only purpose was to supply injectivity, which `TwoSidedIdeal.blockComponentMap_injective` proves directly |
| `MPSTensor.componentMap_injective` (same file) | `TwoSidedIdeal.blockComponentMap_injective` (`QICLean/Algebra/BlockPermutation.lean`) |
| `MPSTensor.componentMap_surjective` (same file) | `TwoSidedIdeal.blockComponentMap_surjective` (`QICLean/Algebra/BlockPermutation.lean`) |
| `MPSTensor.componentMap_bijective` (same file) | `TwoSidedIdeal.blockComponentMap_bijective` (`QICLean/Algebra/BlockPermutation.lean`) |
| `MPSTensor.transferMap_smul_apply` (private, `TNLean/MPS/Symmetry/StringOrderAux.lean`) | `MPSTensor.transferMap_smul` (`TNLean/MPS/SharedInfra/Scaling.lean`) |

One declaration is added: `MPSTensor.SectorDecomposition.mpvState_toTensor_eq_sum_coeff`
in `TNLean/MPS/SharedInfra/SectorDecomposition.lean`, which replaces five
verbatim inline derivations of the same fact.

## What was checked

**Component maps between matched matrix blocks.** The companion library states,
for a ring equivalence between arbitrary products of simple rings, that a tuple
supported in one source factor lands in the paired target factor, and that the
induced component map is injective, surjective and hence bijective. The
tensor-network module restated all four for the homogeneous matrix-algebra case
`∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ`, with proofs that either forwarded
verbatim or reassembled the same pieces: the injectivity restatement built a
ring homomorphism out of the component map only to take its kernel-triviality,
where the companion library proves injectivity directly from the block-support
statement.

The specialization `componentMap` itself stays: it is consumed twice by
`TNLean/MPS/FundamentalTheorem/ProductAlgebra.lean` and it fixes the implicit
data that the general statement leaves open. Because it unfolds to
`blockComponentMap`, the two remaining uses of bijectivity — the
finite-rank comparison in `dim_preserved` and the composition with the
reindexing equivalence in `algEquiv_pi_matrix_decomposition` — accept the
general theorem with no further bridging. The additive and multiplicative
component identities also stay: they are still consumed by the linear map and
the algebra homomorphism built inside those two proofs.

`dim_preserved` has no companion counterpart and is untouched; the companion
library's Skolem–Noether module assumes the dimension equality rather than
proving it.

The blueprint statement of paired component maps carried three `\lean{...}`
tags naming the removed restatements; all three now name the companion
declarations they forwarded to, and the statement prose, its `\leanok`, and the
proof block are unchanged. The dimension-preservation statement and its `\uses`
are untouched.

Two module-docstring corrections travel with this: the file said it connected a
`TNLean.Algebra.BlockPermutation` module, which does not exist — the algebra
layer it builds on is the companion library's — and it advertised the block
ideal membership characterisation as one of its own main results, which the
companion library owns.

**State-vector form of the sector-coefficient expansion.** The pointwise
expansion of the matrix-product vector of an assembled sector tensor into its
basis blocks, weighted by the sector coefficients, was lifted to an equality of
state vectors by the same eight-line block in five places, across three modules:
the basis-of-normal-tensors characterisation, the sector coefficient identity,
and the proportional-match core. Each copy applied the state-vector translation
lemma of the overlap layer to the pointwise expansion and closed the remaining
side goal by the same `simpa`. The lifted statement is now proved once, beside
the pointwise expansion it lifts, in the module that owns both the sector
decomposition and its coefficients; the five sites become one-line `have`s
keeping their binder names.

Two nearby blocks that look similar were left alone: one expands over a
different tensor family, and one routes through a matrix-product-vector
equality rather than the coefficient expansion.

**Transfer-map scaling under a scalar.** Scaling every Kraus matrix of a tensor
by a complex scalar scales the transfer map by the scalar times its conjugate.
This is a public, blueprint-tagged theorem of the shared scaling module; the
string-order auxiliary module carried a byte-identical private copy, down to the
tactic block, because it did not import that module. The private copy is
removed, its single call site names the public theorem — the binder shape is
identical and the rewrite supplies no explicit arguments — and the import is
added. No cycle results: the scaling module is not in the string-order module's
downward closure, and it declares no simp or grind attributes, so no simp set
visible in the string-order module changes. The blueprint tag names the public
theorem, which neither moves nor is renamed. The pattern-ledger entry that cited
the private copy by name now cites the public one.

## Verification

Root `lake build` completes successfully with the package lean options.
`check_forbidden_lean_tokens.py`, `check_reader_facing_prose.py`,
`check_numbered_lean_files.py`, `check_oversized_lean_files.py` and
`generate_import_aggregators.py --check` are clean, and the blueprint
declaration check resolves every tag, including the three redirected ones.
