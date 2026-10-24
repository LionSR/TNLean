/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.OrderedGateLabelPairSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! # Gatewise weights in the ordered ket and bra sum

A product of weights attached to the original gate occurrences can be placed
inside the ordered ket and bra coefficient product. The exterior scalar
remains outside the sum. No weight or coefficient is cancelled, so zero
weights, empty label types and empty gate families are permitted.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 568–588.
-/

namespace TNLean.Lattice.Compression
open scoped ComplexConjugate
variable {G : Type} [Fintype G] {Ket Bra : G → Type}
variable [∀ g, Fintype (Ket g)] [∀ g, Fintype (Bra g)] {m n : Type}

open Classical in
/-- Reindex by ordered gate labels and distribute the gatewise weights into
those coefficients, retaining the exterior scalar multiplicatively.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 568–588. -/
theorem weighted_sum_gateLabels_eq_exterior_smul_orderedGateLabelPairs
    (w : G → ℂ) (γ : ℂ)
    (a : (g : G) → Ket g → ℂ) (b : (g : G) → Bra g → ℂ)
    (K : ((g : G) → Ket g) → ((g : G) → Bra g) → Matrix m n ℂ) :
    ((∏ g, w g) * γ) •
        (∑ η, ∑ θ, (∏ g, a g (η g) * conj (b g (θ g))) • K η θ) =
      γ • ∑ ξζ : (g : G) → Ket g × Bra g,
        (∏ g, w g * a g (ξζ g).1 * conj (b g (ξζ g).2)) •
          K (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) := by
  rw [sum_weighted_gateLabels_eq_sum_orderedGateLabelPairs,
    mul_comm (∏ g, w g) γ, mul_smul]
  apply congrArg (fun Z : Matrix m n ℂ ↦ γ • Z)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ξζ _
  rw [smul_smul, ← Finset.prod_mul_distrib]
  simp only [mul_assoc]

end TNLean.Lattice.Compression
