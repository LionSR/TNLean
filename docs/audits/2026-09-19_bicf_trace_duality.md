# Trace-pairing duality in the block-family separation criteria

Date: 2026-09-19

The finite-word trace separation criteria in
`TNLean/MPS/MPDO/BiCFDerivation/Core.lean` and the simultaneous-span trace
lemma in `TNLean/MPS/SharedInfra/WordTupleGauge.lean` re-derived, by hand,
two facts that the existing matrix trace-pairing interface already supplies:
that every linear functional on a finite matrix algebra is a trace pairing,
and that a trace pairing vanishing on a generating set vanishes on the span
it generates. This pass routes both through that interface. No declaration
was removed, no statement changed, and no blueprint tag moved.

## Rewritten proofs

| Declaration | Former proof | Replacement |
|---|---|---|
| `MPSTensor.exists_trace_repr` (private) | matrix-unit construction of the representing matrix followed by an extensionality argument over single-entry matrices | the inverse of the linear equivalence with the dual space induced by the nondegenerate trace form: `Matrix.traceBilinForm`, `Matrix.traceBilinForm_nondegenerate`, and `LinearMap.BilinForm.apply_toDual_symm_apply` |
| `MPSTensor.exists_pi_trace_repr` (private) | an explicit component-choice hypothesis, a hand-proved decomposition of a family into its single-block pieces, and a sum congruence | `Finset.univ_sum_single` for the decomposition, with the component representations chosen directly from `exists_trace_repr` |
| `MPSTensor.exists_pair_trace_repr` (private) | a two-step calculation restating the functional through its restrictions to the two summands | a rewrite by `LinearMap.coprod_comp_inl_inr` and `LinearMap.coprod_apply` |
| `MPSTensor.pair_trace_zero_on_span` (private) | a four-case span induction repeating additivity and homogeneity of the pair trace pairing | `Submodule.span_le` into the kernel of the coproduct of the two trace forms |
| `MPSTensor.block_matrices_eq_zero_of_wordTupleSpanTop_trace` | a four-case span induction for the block-indexed trace pairing | `Submodule.span_le` into the kernel of the sum over blocks of the trace form composed with the block projection |

Both files now import `QICLean.Algebra.MatrixTracePairing`, which owns the
trace bilinear form and its nondegeneracy.

## Retained and why

Five private helpers in `Core.lean` keep their current proofs:

* `matrix_pi_span_top_of_trace_separating` and
  `pair_matrix_span_top_of_pair_trace_separating` still argue by contradiction
  through a separating functional on a proper submodule. Reducing them to a
  single duality step needs a nondegeneracy statement for the trace form of a
  block-indexed family and for the trace form of a product of two matrix
  algebras. Neither exists upstream: the library owns nondegeneracy only for a
  single matrix algebra, and the product of two matrix algebras is not a
  dependent family over a two-element index type, so the product case needs its
  own form.
* `eq_zero_and_eq_zero_of_pair_trace_eq_zero` is the converse direction and is
  already a two-line consequence of matrix extensionality against trace
  pairings.
* `exists_pi_trace_repr` and `exists_pair_trace_repr` survive as the indexed
  corollaries of `exists_trace_repr`; they would be retired together with the
  two separation helpers by the same upstream addition.

## Checked

* Both edited modules and every module importing either of them build with the
  package linter options.
* The nine public consumers in `Core.lean` and the two public consumers of the
  simultaneous-span trace lemma keep their names, statements, and proofs, so the
  blueprint nodes tagging them are unaffected.
* No declaration is removed, so no deprecation alias question arises.

## Deferred

An upstream addition of a block-indexed trace form and a product trace form,
each with nondegeneracy and the corresponding span criterion, would retire the
five retained helpers and the corresponding private representation helper that
the upstream library carries for its own span arguments.
