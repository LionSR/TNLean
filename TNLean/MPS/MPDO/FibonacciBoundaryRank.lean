/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PureRecovery
import Mathlib.Tactic.FinCases

/-!
# Fibonacci boundary rank calculation

This file formalizes the concrete vacuum-sector calculation in CPSV16 Appendix D.
The three binary physical labels are written `i,j,k`, the fusion weights are
`N_{ijk}`, and the virtual labels are `α,β`.  The local tensor is
`A^{ijk}_{αβ} = δ_{i,α} δ_{k,β} N_{ijk}`.  We do not define the diagrammatic
``Strong-RFP`` condition.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix D, lines 2116--2176, labels `rank-Fibonacci` and `eq:1`.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

namespace MPSTensor
namespace FibonacciBoundary

/-- Exactly two of the three Fibonacci fusion labels are zero.

Source: arXiv:1606.00608, Appendix D, lines 2133--2135. -/
def ExactlyTwoZero (i j k : Fin 2) : Prop :=
  (i = 0 ∧ j = 0 ∧ k = 1) ∨ (i = 0 ∧ j = 1 ∧ k = 0) ∨
    (i = 1 ∧ j = 0 ∧ k = 0)

/-- Positive fusion weights `N_{ijk}` with exactly the support prescribed by the
Fibonacci fusion rules.

Source: arXiv:1606.00608, Appendix D, lines 2131--2135. -/
structure FusionWeights where
  N : Fin 2 → Fin 2 → Fin 2 → ℝ
  zero_iff : ∀ i j k, N i j k = 0 ↔ ExactlyTwoZero i j k
  pos_of_not_exactlyTwoZero : ∀ i j k, ¬ExactlyTwoZero i j k → 0 < N i j k

/-- The canonical `0/1` Fibonacci fusion weights. -/
noncomputable def canonicalFusionWeights : FusionWeights := by
  classical
  exact {
    N := fun i j k ↦ if ExactlyTwoZero i j k then 0 else 1
    zero_iff := fun i j k ↦ by simp
    pos_of_not_exactlyTwoZero := fun i j k h ↦ by simp [h] }

/-- Decode the physical label into the paper's three binary labels `(i,j,k)`. -/
def physicalTriple (p : Fin 8) : Fin 2 × Fin 2 × Fin 2 :=
  (⟨p.val / 4, by omega⟩, ⟨(p.val / 2) % 2, Nat.mod_lt _ (by omega)⟩,
    ⟨p.val % 2, Nat.mod_lt _ (by omega)⟩)

/-- The source tensor `A^{ijk}_{αβ} = δ_{i,α}δ_{k,β}N_{ijk}`.

Source: arXiv:1606.00608, Appendix D, lines 2119--2135. -/
noncomputable def tensor (W : FusionWeights) : MPSTensor 8 2 := fun p α β =>
  let ijk := physicalTriple p
  if ijk.1 = α ∧ ijk.2.2 = β then (W.N ijk.1 ijk.2.1 ijk.2.2 : ℂ) else 0

/-- The canonical support tensor, with every allowed `N_{ijk}` equal to one. -/
noncomputable abbrev canonicalTensor : MPSTensor 8 2 := tensor canonicalFusionWeights

/-- The two-state transfer matrix `B = [[1,1],[1,2]]` from the source calculation.

Source: arXiv:1606.00608, Appendix D, lines 2154--2164. -/
def B : Matrix (Fin 2) (Fin 2) ℕ := !![1, 1; 1, 2]

/-- The transition counts `x^n_{αβ}` from the source open-boundary recurrence.
Their identification with the ranks of the concrete open-boundary operators is
left to the remaining rank bridge.

Source: arXiv:1606.00608, Appendix D, lines 2139--2164. -/
def x (n : ℕ) (α β : Fin 2) : ℕ := (B ^ n) α β

/-- The source initial value `x¹ = (1,1,1,2)`. -/
theorem x_one :
    (x 1 0 0, x 1 0 1, x 1 1 0, x 1 1 1) = (1, 1, 1, 2) := by
  norm_num [x, B]

/-- The source recurrence `xⁿ = xⁿ⁻¹ B`, simultaneously for all boundary
conditions.

Source: arXiv:1606.00608, Appendix D, lines 2146--2164. -/
theorem x_succ (n : ℕ) (α : Fin 2) :
    x (n + 1) α 0 = x n α 0 + x n α 1 ∧
      x (n + 1) α 1 = x n α 0 + 2 * x n α 1 := by
  fin_cases α <;>
    simp [x, pow_succ, B, Matrix.mul_apply, Fin.sum_univ_two] <;> omega

/-- The periodic transition count is extracted by closing the two boundary
labels, `a_N = x^N_{00} + x^N_{11}`.  The source identifies this count with
`rank ρ^(N)`; that operator-rank bridge remains separate.

Source: arXiv:1606.00608, Appendix D, lines 2164--2176. -/
def periodicRank (N : ℕ) : ℕ := x N 0 0 + x N 1 1

/-- The first periodic rank is three. -/
@[simp] theorem periodicRank_one : periodicRank 1 = 3 := by
  norm_num [periodicRank, x, B]

/-- The second periodic rank is seven. -/
@[simp] theorem periodicRank_two : periodicRank 2 = 7 := by
  rw [periodicRank, (x_succ 1 0).1, (x_succ 1 1).2]
  norm_num [x, B]

/-- The Fibonacci periodic ranks cannot have geometric growth `r s^(N-1)`.
The contradiction is already forced by ranks three and seven.

Source: arXiv:1606.00608, Appendix D, lines 2136--2140. -/
theorem periodicRank_not_geometric :
    ¬∃ r s : ℕ, ∀ N : ℕ, 0 < N → periodicRank N = r * s ^ (N - 1) := by
  rintro ⟨r, s, h⟩
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  simp only [periodicRank_one, periodicRank_two, Nat.reduceSubDiff, pow_zero, pow_one,
    mul_one] at h1 h2
  subst r
  omega

end FibonacciBoundary
end MPSTensor
