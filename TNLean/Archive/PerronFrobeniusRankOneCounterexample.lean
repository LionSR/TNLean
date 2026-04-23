/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Counterexample: primitivity plus constant trace powers does not imply rank one

The standalone matrix statement

    `Matrix.IsPrimitive T → Matrix.TracePowersConstant T → HasRankOneFactorization T`

corresponding to `Matrix.PrimitiveTracePowersConstantImpliesRankOne` in
`TNLean/MPS/MPDO/SimpleLocalStructure.lean` is **false** for a general
primitive nonnegative real matrix. This module exhibits an explicit `3 × 3`
nonnegative primitive matrix `T` with

* all entries of `T ^ 2` strictly positive, so `T` is primitive in the sense of
  `Mathlib.Matrix.IsPrimitive`;
* `trace (T ^ k) = trace T = 1` for every `k ≥ 1`;
* `T` of rank two — no rank-one factorization `T = vecMulVec a b` exists.

Concretely, `T = P + (1/6) · N` where `P = (1/3) · J` is the Perron projector
(`J` the `3 × 3` all-ones matrix) and `N = x · yᵀ` with `x = (1, -1, 0)`,
`y = (1, 1, -2)`. One checks `N² = 0`, `P N = N P = 0`, `P² = P`, so
`T ^ k = P` for all `k ≥ 2`, while `T` itself has a non-trivial Jordan block
for the zero eigenvalue and thus rank two.

This module documents the gap in the Appendix C.2, Lemma C.4 argument of
arXiv:1606.00608: primitivity and constant trace powers alone are not
sufficient; additional structure on `T` (for example positive
semidefiniteness, or diagonalizability over `ℂ`) is required to close the
rank-one step.

This file is deliberately excluded from the root `TNLean.lean` import list.

## References

- arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete), Appendix C.2,
  Lemma C.4
- Issue #832 on the TNLean repository

## Main results

* `counterexample`: the explicit witness to the failure of the stated
  implication.
-/

namespace TNLean.Archive.PerronFrobeniusRankOneCounterexample

open Matrix

/-- The counterexample matrix. -/
noncomputable def T : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2, 1/2, 0; 1/6, 1/6, 2/3; 1/3, 1/3, 1/3]

/-- The rank-one Perron projector for `T`, equal to `T ^ k` for every `k ≥ 2`. -/
noncomputable def P : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/3, 1/3, 1/3; 1/3, 1/3, 1/3; 1/3, 1/3, 1/3]

lemma T_sq : T * T = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, P, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

lemma T_mul_P : T * P = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, P, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

lemma P_mul_T : P * T = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, P, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

lemma T_nonneg (i j : Fin 3) : 0 ≤ T i j := by
  fin_cases i <;> fin_cases j <;>
    first
    | (simp [T]; norm_num)
    | simp [T]

lemma T_pow2_pos (i j : Fin 3) : 0 < (T ^ 2) i j := by
  have h : T ^ 2 = P := by rw [sq]; exact T_sq
  rw [h]
  fin_cases i <;> fin_cases j <;> simp [P]

/-- `T` is primitive in Mathlib's sense. -/
theorem T_isPrimitive : Matrix.IsPrimitive T :=
  ⟨T_nonneg, 2, by norm_num, T_pow2_pos⟩

lemma T_pow_eq_P : ∀ k : ℕ, 2 ≤ k → T ^ k = P := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le hk with h | h
    · rw [← h, sq]; exact T_sq
    · have h2 : 2 ≤ n := by omega
      rw [pow_succ, ih h2]
      exact P_mul_T

lemma trace_T : Matrix.trace T = 1 := by
  simp [Matrix.trace, T, Fin.sum_univ_three]; ring

lemma trace_P : Matrix.trace P = 1 := by
  simp [Matrix.trace, P, Fin.sum_univ_three]; ring

/-- Every positive power of `T` has the same trace as `T`. -/
theorem T_tracePowersConstant :
    ∀ k : ℕ, 0 < k → Matrix.trace (T ^ k) = Matrix.trace T := by
  intro k hk
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k; simp
  · rw [T_pow_eq_P k h, trace_T, trace_P]

/-- `T` has no rank-one factorization. -/
theorem T_not_rankOne : ¬ ∃ a b : Fin 3 → ℝ, T = Matrix.vecMulVec a b := by
  rintro ⟨a, b, hT⟩
  have h00 : a 0 * b 0 = (1 : ℝ) / 2 := by
    have hh : T 0 0 = Matrix.vecMulVec a b 0 0 := by rw [hT]
    simp [T, Matrix.vecMulVec_apply] at hh
    linarith
  have h02 : a 0 = 0 ∨ b 2 = 0 := by
    have hh : T 0 2 = Matrix.vecMulVec a b 0 2 := by rw [hT]
    simpa [T, Matrix.vecMulVec_apply] using hh
  have h12 : a 1 * b 2 = (2 : ℝ) / 3 := by
    have hh : T 1 2 = Matrix.vecMulVec a b 1 2 := by rw [hT]
    simp [T, Matrix.vecMulVec_apply] at hh
    linarith
  have ha0 : a 0 ≠ 0 := fun h => by
    rw [h, zero_mul] at h00; norm_num at h00
  have hb2 : b 2 = 0 := h02.resolve_left ha0
  rw [hb2, mul_zero] at h12
  norm_num at h12

/-- The explicit counterexample to the standalone statement of
`Matrix.PrimitiveTracePowersConstantImpliesRankOne`: `T` is primitive,
satisfies the constant-trace-powers hypothesis, yet has no rank-one
factorization. -/
theorem counterexample :
    Matrix.IsPrimitive T ∧
      (∀ k : ℕ, 0 < k → Matrix.trace (T ^ k) = Matrix.trace T) ∧
      ¬ ∃ a b : Fin 3 → ℝ, T = Matrix.vecMulVec a b :=
  ⟨T_isPrimitive, T_tracePowersConstant, T_not_rankOne⟩

end TNLean.Archive.PerronFrobeniusRankOneCounterexample
