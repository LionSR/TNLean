/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Chain.Defs

/-!
# Tensor proportionality from matching virtual insertions

This file provides the **tensor proportionality** lemma for injective MPS tensors
(Issue #7). The main result: if two injective tensors at adjacent sites agree on
all virtual insertions (i.e. for every matrix `X` inserted on the bond between
them, the resulting coefficients agree), then the tensors at each site are
proportional.

## Main results

* `MPSTensor.tensor_proportional` — if two injective tensors `A`, `B` agree on
  all virtual-insertion coefficients, then `A i = λ • B i` for some nonzero `λ`.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), §III
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Virtual insertion coefficient for a 2-site chain:
`Tr(A(σ₀) · X · B(σ₁))` where `X` is inserted on the bond between the two
sites. -/
noncomputable def virtualInsert2 (A B : MPSTensor d D)
    (σ₀ σ₁ : Fin d) (X : Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  Matrix.trace (A σ₀ * X * B σ₁)

/-- Tensor proportionality from matching virtual insertions.

If two injective tensors `A` and `B` agree on all 2-site virtual-insertion
coefficients — i.e. `∀ X σ₀ σ₁, Tr(A(σ₀) X A_right(σ₁)) = Tr(B(σ₀) X B_right(σ₁))`
— then `A` and `B` are proportional: there exists a nonzero scalar `λ` such
that `A i = λ • B i` for all `i`. -/
theorem tensor_proportional
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hInsert : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (σ₀ σ₁ : Fin d),
      virtualInsert2 A A σ₀ σ₁ X = virtualInsert2 B B σ₀ σ₁ X) :
    ∃ λ_ : ℂ, λ_ ≠ 0 ∧ ∀ i : Fin d, A i = λ_ • B i := by
  sorry

end MPSTensor
