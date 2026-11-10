/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.IrreducibleTensor

/-!
# Schur's lemma for irreducible tensors, with the gauge relation

An intertwiner `X C^i = C'^i X` of two irreducible tensors is zero or invertible, and in the second
case the two tensors are gauge related. The kernel of `X` is invariant under the letters
of `C` and its range under those of `C'`; this is
`MPSTensor.eq_zero_or_exists_inverse_of_intertwines`, and the inverse of `X` gives the gauge
relation.

## Main results

* `MPSTensor.eq_zero_or_isGaugeRelated_of_intertwines_of_isIrreducibleAction`.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Schur's lemma.** If `C` and `C'` are irreducible and the
rectangular matrix `X` satisfies `X C^i = C'^i X` for every letter, then `X = 0`, or `X` has a
two-sided inverse and `C` is gauge related to `C'`. For bond dimension zero the irreducibility
hypotheses hold vacuously and the statement is still true. -/
theorem eq_zero_or_isGaugeRelated_of_intertwines_of_isIrreducibleAction {D D' : ℕ}
    {C : MPSTensor d D} {C' : MPSTensor d D'} (hC : Matrix.IsIrreducibleAction C)
    (hC' : Matrix.IsIrreducibleAction C') {X : Matrix (Fin D') (Fin D) ℂ}
    (hX : ∀ i, X * C i = C' i * X) :
    X = 0 ∨ ((∃ Y : Matrix (Fin D) (Fin D') ℂ, X * Y = 1 ∧ Y * X = 1) ∧ IsGaugeRelated C C') := by
  rcases eq_zero_or_exists_inverse_of_intertwines hC hC' hX with h | ⟨Y, hXY, hYX, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨Y, hXY, hYX⟩, IsGaugeRelated.symm ⟨X, Y, hXY, hYX, fun i => (hX i).symm⟩⟩

end MPSTensor
