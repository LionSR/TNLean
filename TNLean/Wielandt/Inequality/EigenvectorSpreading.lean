/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.Inequality.EigenvectorSpreading
import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.MPS.Tensor

/-!
# Lemma 2(a) for MPS tensors

This file retains the MPS formulation of Lemma 2(a) from
Sanz--Pérez-García--Wolf--Cirac, *A quantum version of Wielandt's inequality*
(arXiv:0909.5347). Its finite-Kraus content is proved in
`Kraus.vectorSpreadSpan_eq_top_of_hasEventuallyFullWordSpan_of_eigenvector`.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- **Lemma 2(a)**.

If `A` is normalized and normal (a primitive channel, by Proposition 3 of the
source, `primitivity_tfae`), and `φ` is a nonzero
eigenvector of some `A i₀` with nonzero corresponding eigenvalue `μ`, then
`Kraus.vectorSpreadSpan A φ (D - 1) = ⊤`.

This is the fixed-length conclusion `H_{D-1}(A, φ) = ℂ^D`.
Paper: arXiv:0909.5347, Lemma 2(a); Wolf, Chapter 6. -/
theorem vectorSpreadSpan_eq_top_of_isNormal_of_eigenvector [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hN : Kraus.IsNormal A)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    (i₀ : Fin d) (μ : ℂ) (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    Kraus.vectorSpreadSpan A φ (D - 1) = ⊤ := by
  have hFull : Kraus.HasEventuallyFullWordSpan A :=
    (Kraus.hasEventuallyFullWordSpan_iff_exists_pos_of_isTP A hNorm).2 hN
  exact
    Kraus.vectorSpreadSpan_eq_top_of_hasEventuallyFullWordSpan_of_eigenvector
      A hFull φ hφ i₀ μ hμ heig

end MPSTensor
