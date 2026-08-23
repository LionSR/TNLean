/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Fibonacci boundary transition calculation

This file formalizes the concrete vacuum-sector calculation in CPSV16 Appendix D.
The three binary physical labels are written \(i,j,k\), the fusion weights are
\(N_{ijk}\), and the virtual labels are \(α,β\).  The local tensor is
\(A^{ijk}_{αβ} = δ_{i,α} δ_{k,β} N_{ijk}\).  The structural strong fixed-point
relation is defined separately in `MPOTensor.IsStrongRFP`.

The open-boundary calculation identifies the transition count with the ordinary
matrix rank of the source diagonal operator. The periodic operator-rank identity is
not established here, so the golden-ratio formula remains a transition-count theorem.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix D, lines 2116--2176.
-/

open scoped Matrix
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
  /-- The fusion coefficient assigned to the labels \((i,j,k)\). -/
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

private instance (i j k : Fin 2) : Decidable (ExactlyTwoZero i j k) := by
  unfold ExactlyTwoZero
  infer_instance

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

/-- Whether a physical word contributes to the open-boundary contraction. -/
private def isSupportedWord (α β : Fin 2) : List (Fin 8) → Bool
  | [] => α == β
  | p :: w =>
      let ijk := physicalTriple p
      ijk.1 == α && !(decide (ExactlyTwoZero ijk.1 ijk.2.1 ijk.2.2)) &&
        isSupportedWord ijk.2.2 β w

/-- The number of supported physical words of length \(n\) with fixed virtual endpoints. -/
private def supportedCount (n : ℕ) (α β : Fin 2) : ℕ :=
  ∑ σ : Fin n → Fin 8, if isSupportedWord α β (List.ofFn σ) then 1 else 0

@[simp] private lemma supportedCount_zero (α β : Fin 2) :
    supportedCount 0 α β = if α = β then 1 else 0 := by
  simp [supportedCount, isSupportedWord]

private lemma supportedCount_succ (n : ℕ) (α β : Fin 2) :
    supportedCount (n + 1) α β =
      (if α = 0 then supportedCount n 0 β + supportedCount n 1 β
       else supportedCount n 0 β + 2 * supportedCount n 1 β) := by
  rw [supportedCount]
  rw [Fintype.sum_equiv (finSuccArrowEquiv (Fin 8) n)
    (fun σ : Fin (n + 1) → Fin 8 =>
      if isSupportedWord α β (List.ofFn σ) then 1 else 0)
    (fun p : Fin 8 × (Fin n → Fin 8) =>
      if isSupportedWord α β (List.ofFn (Fin.cons p.1 p.2)) then 1 else 0)]
  · simp only [List.ofFn_succ, Fin.cons_zero]
    change (∑ p : Fin 8 × (Fin n → Fin 8),
      if isSupportedWord α β (p.1 :: List.ofFn p.2) then 1 else 0) = _
    rw [Fintype.sum_prod_type]
    fin_cases α
    · simp [isSupportedWord, physicalTriple, ExactlyTwoZero, supportedCount,
        Fin.sum_univ_eight]
    · simp [isSupportedWord, physicalTriple, ExactlyTwoZero, supportedCount,
        Fin.sum_univ_eight]
      omega
  · intro σ
    simp

private lemma tensor_mul_apply_ne_zero_iff (W : FusionWeights) (p : Fin 8)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (α β : Fin 2) :
    (tensor W p * M) α β ≠ 0 ↔
      (physicalTriple p).1 = α ∧
        ¬ExactlyTwoZero (physicalTriple p).1 (physicalTriple p).2.1
          (physicalTriple p).2.2 ∧
        M (physicalTriple p).2.2 β ≠ 0 := by
  fin_cases p <;> fin_cases α <;> fin_cases β <;>
    simp [Matrix.mul_apply, tensor, physicalTriple, W.zero_iff, ExactlyTwoZero]

private lemma evalWord_apply_ne_zero_iff (W : FusionWeights) (w : List (Fin 8))
    (α β : Fin 2) : Kraus.evalWord (tensor W) w α β ≠ 0 ↔ isSupportedWord α β w := by
  induction w generalizing α with
  | nil =>
      fin_cases α <;> fin_cases β <;> simp [Kraus.evalWord, isSupportedWord]
  | cons p w ih =>
      rw [Kraus.evalWord_cons, tensor_mul_apply_ne_zero_iff, ih]
      simp only [isSupportedWord, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        beq_iff_eq]
      tauto

/-- A nonempty physical word cannot contribute to both closed virtual endpoints.

This is the endpoint-support fact needed to split the periodic trace support into
its two diagonal boundary sectors. -/
lemma evalWord_closed_endpoint_support_disjoint (W : FusionWeights) (p : Fin 8)
    (w : List (Fin 8)) :
    ¬(Kraus.evalWord (tensor W) (p :: w) 0 0 ≠ 0 ∧
      Kraus.evalWord (tensor W) (p :: w) 1 1 ≠ 0) := by
  rw [evalWord_apply_ne_zero_iff, evalWord_apply_ne_zero_iff]
  simp only [isSupportedWord, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, beq_iff_eq]
  omega

private lemma supportedCount_eq_x (n : ℕ) (α β : Fin 2) :
    supportedCount n α β = x n α β := by
  induction n generalizing α with
  | zero =>
      fin_cases α <;> fin_cases β <;> simp [x]
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, supportedCount_succ]
      fin_cases α <;> fin_cases β <;>
        simp only [ih]
      all_goals simp [x, pow_succ', B, Matrix.mul_apply, Fin.sum_univ_two]

/-- The source diagonal open-boundary operator with fixed virtual endpoints.
Its diagonal entry at \(σ\) is the word amplitude
\((\alpha|A^{σ_1}\cdots A^{σ_n}|\beta)\), and every off-diagonal entry is zero.

Source: arXiv:1606.00608, Appendix D, lines 2127--2130. -/
noncomputable def openBoundaryOperator (W : FusionWeights) (n : ℕ) (α β : Fin 2) :
    Matrix (Fin n → Fin 8) (Fin n → Fin 8) ℂ :=
  Matrix.diagonal fun σ => Kraus.evalWord (tensor W) (List.ofFn σ) α β

@[simp] theorem openBoundaryOperator_apply (W : FusionWeights) (n : ℕ) (α β : Fin 2)
    (σ τ : Fin n → Fin 8) :
    openBoundaryOperator W n α β σ τ =
      if σ = τ then Kraus.evalWord (tensor W) (List.ofFn σ) α β else 0 := by
  rw [openBoundaryOperator, Matrix.diagonal_apply]

/-- The ordinary matrix rank of the source diagonal open-boundary operator is
\(x^n_{αβ}\).

Source: arXiv:1606.00608, Appendix D, lines 2127--2130. -/
theorem rank_openBoundaryOperator_eq_x (W : FusionWeights) (n : ℕ) (α β : Fin 2) :
    (openBoundaryOperator W n α β).rank = x n α β := by
  classical
  rw [openBoundaryOperator, Matrix.rank_diagonal, Fintype.card_subtype]
  rw [← supportedCount_eq_x n α β]
  simp only [supportedCount, evalWord_apply_ne_zero_iff]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

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

/-- The periodic transition counts satisfy the characteristic recurrence of
\(B=\left(\begin{smallmatrix}1&1\\1&2\end{smallmatrix}\right)\).

Source: arXiv:1606.00608, Appendix D, lines 2146--2149. -/
theorem periodicTransitionCount_add_two_add (N : ℕ) :
    periodicTransitionCount (N + 2) + periodicTransitionCount N =
      3 * periodicTransitionCount (N + 1) := by
  simp [periodicTransitionCount, x, show N + 2 = N + 1 + 1 by omega, pow_succ, B,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The exact closed formula for the periodic transition count is the sum of the
\(2N\)-th powers of the golden ratio and its conjugate. This is only the
transition-count slice of the calculation and does not identify these counts with
MPO operator ranks.

Source: CPSV16, arXiv:1606.00608v4, Appendix D, lines 2146--2176. -/
theorem periodicTransitionCount_eq_goldenRatio (N : ℕ) :
    (periodicTransitionCount N : ℝ) =
      Real.goldenRatio ^ (2 * N) + Real.goldenConj ^ (2 * N) := by
  induction N using Nat.twoStepInduction with
  | zero => norm_num [periodicTransitionCount, x, B]
  | one =>
      norm_num [periodicTransitionCount, x, B]
      nlinarith [Real.goldenRatio_sq, Real.goldenConj_sq,
        Real.goldenRatio_add_goldenConj]
  | more N hN hN1 =>
      have hCount := congrArg (fun n : ℕ ↦ (n : ℝ)) (periodicTransitionCount_add_two_add N)
      push_cast at hCount
      have hRootPowers (z : ℝ) (hz : z ^ 2 = z + 1) :
          z ^ (2 * (N + 2)) + z ^ (2 * N) = 3 * z ^ (2 * (N + 1)) := by
        have hQuartic : z ^ 4 + 1 = 3 * z ^ 2 := by
          linear_combination (z ^ 2 + z - 1) * hz
        rw [show 2 * (N + 2) = 2 * N + 4 by omega,
          show 2 * (N + 1) = 2 * N + 2 by omega, pow_add, pow_add]
        linear_combination z ^ (2 * N) * hQuartic
      have hRatio := hRootPowers Real.goldenRatio Real.goldenRatio_sq
      have hConj := hRootPowers Real.goldenConj Real.goldenConj_sq
      rw [hN, hN1] at hCount
      linarith

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
