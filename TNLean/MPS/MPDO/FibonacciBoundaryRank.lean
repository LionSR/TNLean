/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PureRecovery
import Mathlib.Tactic.FinCases

/-!
# Fibonacci boundary transition calculation

This file formalizes the concrete vacuum-sector calculation in CPSV16 Appendix D.
The three binary physical labels are written \(i,j,k\), the fusion weights are
\(N_{ijk}\), and the virtual labels are \(α,β\).  The local tensor is
\(A^{ijk}_{αβ} = δ_{i,α} δ_{k,β} N_{ijk}\).  The structural strong fixed-point
relation is defined separately in `MPOTensor.IsStrongRFP`.

**Scope restriction (transition-count slice):** This file does not identify the
transition counts with the open-boundary or periodic operator ranks, and it does
not prove the golden-ratio formula for the periodic rank.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix D, lines 2116--2176.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

namespace MPSTensor
namespace FibonacciBoundary

/-- Exactly two of the three Fibonacci fusion labels are zero.

Source: arXiv:1606.00608, Appendix D, lines 2120--2121. -/
def ExactlyTwoZero (i j k : Fin 2) : Prop :=
  (i = 0 ∧ j = 0 ∧ k = 1) ∨ (i = 0 ∧ j = 1 ∧ k = 0) ∨
    (i = 1 ∧ j = 0 ∧ k = 0)

/-- Positive fusion weights \(N_{ijk}\) with exactly the support prescribed by the
Fibonacci fusion rules.

Source: arXiv:1606.00608, Appendix D, lines 2120--2121. -/
structure FusionWeights where
  N : Fin 2 → Fin 2 → Fin 2 → ℝ
  zero_iff : ∀ i j k, N i j k = 0 ↔ ExactlyTwoZero i j k
  pos_of_not_exactlyTwoZero : ∀ i j k, ¬ExactlyTwoZero i j k → 0 < N i j k

/-- The canonical \(0/1\) Fibonacci fusion weights. -/
noncomputable def canonicalFusionWeights : FusionWeights := by
  classical
  exact {
    N := fun i j k ↦ if ExactlyTwoZero i j k then 0 else 1
    zero_iff := fun i j k ↦ by simp
    pos_of_not_exactlyTwoZero := fun i j k h ↦ by simp [h] }

/-- Decode the physical label into the paper's three binary labels \((i,j,k)\). -/
def physicalTriple (p : Fin 8) : Fin 2 × Fin 2 × Fin 2 :=
  (⟨p.val / 4, by omega⟩, ⟨(p.val / 2) % 2, Nat.mod_lt _ (by omega)⟩,
    ⟨p.val % 2, Nat.mod_lt _ (by omega)⟩)

/-- The source tensor \(A^{ijk}_{αβ} = δ_{i,α}δ_{k,β}N_{ijk}\).

Source: arXiv:1606.00608, Appendix D, lines 2116--2121. -/
noncomputable def tensor (W : FusionWeights) : MPSTensor 8 2 := fun p α β =>
  let ijk := physicalTriple p
  if ijk.1 = α ∧ ijk.2.2 = β then (W.N ijk.1 ijk.2.1 ijk.2.2 : ℂ) else 0

/-- The canonical support tensor, with every allowed \(N_{ijk}\) equal to one. -/
noncomputable abbrev canonicalTensor : MPSTensor 8 2 := tensor canonicalFusionWeights

/-- The two-state transition matrix
\(B=\left(\begin{smallmatrix}1&1\\1&2\end{smallmatrix}\right)\) from the source
calculation.

Source: arXiv:1606.00608, Appendix D, lines 2146--2149. -/
def B : Matrix (Fin 2) (Fin 2) ℕ := !![1, 1; 1, 2]

/-- The transition counts \(x^n_{αβ}\) satisfying the source open-boundary
recurrence.  This definition records the matrix-power counts only; it makes no
identification with the ranks of open-boundary operators.

Source: arXiv:1606.00608, Appendix D, lines 2127--2149. -/
def x (n : ℕ) (α β : Fin 2) : ℕ := (B ^ n) α β

/-- The source initial value \(x^1=(1,1,1,2)\).

Source: arXiv:1606.00608, Appendix D, lines 2138--2145. -/
theorem x_one :
    (x 1 0 0, x 1 0 1, x 1 1 0, x 1 1 1) = (1, 1, 1, 2) := by
  norm_num [x, B]

/-- The source recurrence \(x^n=x^{n-1}B\), simultaneously for all boundary
conditions.

Source: arXiv:1606.00608, Appendix D, lines 2131--2149. -/
theorem x_succ (n : ℕ) (α : Fin 2) :
    x (n + 1) α 0 = x n α 0 + x n α 1 ∧
      x (n + 1) α 1 = x n α 0 + 2 * x n α 1 := by
  fin_cases α <;>
    simp [x, pow_succ, B, Matrix.mul_apply, Fin.sum_univ_two] <;> omega

/-- The periodic transition count obtained by closing the two boundary labels,
\(a_N=x^N_{00}+x^N_{11}\).  This definition asserts only the transition count,
not an operator-rank identity.

Source: arXiv:1606.00608, Appendix D, lines 2157--2176. -/
def periodicTransitionCount (N : ℕ) : ℕ := x N 0 0 + x N 1 1

/-- The first periodic transition count is three. -/
@[simp] theorem periodicTransitionCount_one : periodicTransitionCount 1 = 3 := by
  norm_num [periodicTransitionCount, x, B]

/-- The second periodic transition count is seven. -/
@[simp] theorem periodicTransitionCount_two : periodicTransitionCount 2 = 7 := by
  rw [periodicTransitionCount, (x_succ 1 0).1, (x_succ 1 1).2]
  norm_num [x, B]

/-- The periodic transition counts cannot have geometric growth \(r s^{N-1}\).
The contradiction is already forced by the values three and seven.

Source: arXiv:1606.00608, Appendix D, line 2125. -/
theorem periodicTransitionCount_not_geometric :
    ¬∃ r s : ℕ, ∀ N : ℕ, 0 < N → periodicTransitionCount N = r * s ^ (N - 1) := by
  rintro ⟨r, s, h⟩
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  simp only [periodicTransitionCount_one, periodicTransitionCount_two, Nat.reduceSubDiff,
    pow_zero, pow_one, mul_one] at h1 h2
  subst r
  omega

end FibonacciBoundary
end MPSTensor
