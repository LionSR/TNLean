/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Counterexample: primitivity plus constant trace powers does not imply rank one

The standalone matrix statement

    `Matrix.IsPrimitive T → Matrix.TracePowersConstant T → HasRankOneFactorization T`

formerly proposed in the active development is **false** for a general
primitive nonnegative real matrix. This module exhibits an explicit `3 × 3`
nonnegative primitive matrix `T` with

* all entries of `T ^ 2` strictly positive, so `T` is primitive in the sense of
  `Mathlib.Matrix.IsPrimitive`;
* `trace (T ^ k) = trace T = 1` for every `k ≥ 1`;
* `T` of rank two — no rank-one factorization `T = vecMulVec a b` exists.
* explicit rectangular factors `pairingL` and `pairingR` such that
  `T = pairingR * pairingL` and `pairingL * pairingR` is idempotent.

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
* `counterexample_with_rectangular_pairing`: the same witness satisfies the
  full rectangular pairing identity used at source lines 1490--1497.
-/

namespace TNLean.Archive.PerronFrobeniusRankOneCounterexample

open Matrix

/-- The counterexample matrix. -/
noncomputable def T : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2, 1/2, 0; 1/6, 1/6, 2/3; 1/3, 1/3, 1/3]

/-- The rank-one Perron projector for `T`, equal to `T ^ k` for every `k ≥ 2`. -/
noncomputable def P : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/3, 1/3, 1/3; 1/3, 1/3, 1/3; 1/3, 1/3, 1/3]

/-- The coefficient-side factor in the rectangular pairing realization of
`T`. Together with `pairingR`, it realizes the operator identity used in
arXiv:1606.00608, Appendix C.2, lines 1490--1497. -/
noncomputable def pairingL : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1/3, 1/3, 1/3; 1/6, 1/6, -1/3]

/-- The functional-side factor in the rectangular pairing realization of
`T` from arXiv:1606.00608, Appendix C.2, lines 1490--1497. -/
noncomputable def pairingR : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, 1; 1, -1; 1, 0]

/-- The idempotent product in the bond space for the rectangular pairing
realization of arXiv:1606.00608, Appendix C.2, lines 1490--1493. -/
noncomputable def pairingIdempotent : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 0]

lemma pairingR_mul_pairingL : pairingR * pairingL = T := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairingR, pairingL, T, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma pairingL_mul_pairingR : pairingL * pairingR = pairingIdempotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairingL, pairingR, pairingIdempotent, Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring

/-- The product in the opposite order is idempotent, exactly as in the
operator identity of arXiv:1606.00608, Appendix C.2, lines 1490--1493. -/
theorem pairingL_mul_pairingR_isIdempotent :
    IsIdempotentElem (pairingL * pairingR) := by
  rw [pairingL_mul_pairingR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairingIdempotent, Matrix.mul_apply, Fin.sum_univ_two]

lemma T_sq : T * T = P := by
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

/-- The explicit counterexample to the standalone implication above: `T` is
primitive, satisfies the constant-trace-powers hypothesis, yet has no rank-one
factorization. -/
theorem counterexample :
    Matrix.IsPrimitive T ∧
      (∀ k : ℕ, 0 < k → Matrix.trace (T ^ k) = Matrix.trace T) ∧
      ¬ ∃ a b : Fin 3 → ℝ, T = Matrix.vecMulVec a b :=
  ⟨T_isPrimitive, T_tracePowersConstant, T_not_rankOne⟩

/-- The primitive trace-normalized counterexample satisfies the full
rectangular pairing identity used in arXiv:1606.00608, Appendix C.2, lines
1490--1497: `T = pairingR * pairingL`, while the product in the opposite order
is idempotent. Nevertheless `T` is not an outer product. Thus the rectangular
identity proves the trace-power display at lines 1494--1497, but does not prove
the rank-one assertion at lines 1498--1499. -/
theorem counterexample_with_rectangular_pairing :
    Matrix.IsPrimitive T ∧
      Matrix.trace T = 1 ∧
      (∀ k : ℕ, 0 < k → Matrix.trace (T ^ k) = Matrix.trace T) ∧
      T = pairingR * pairingL ∧
      IsIdempotentElem (pairingL * pairingR) ∧
      ¬ ∃ a b : Fin 3 → ℝ, T = Matrix.vecMulVec a b :=
  ⟨T_isPrimitive, trace_T, T_tracePowersConstant, pairingR_mul_pairingL.symm,
    pairingL_mul_pairingR_isIdempotent, T_not_rankOne⟩

end TNLean.Archive.PerronFrobeniusRankOneCounterexample
