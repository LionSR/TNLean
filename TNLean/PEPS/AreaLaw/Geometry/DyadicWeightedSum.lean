/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.GeomSum

/-!
# Finite weighted dyadic sums

A cap-scale side budget `A` and a uniform lower-scale side budget `B` give
an explicit bound on the sum of side lengths to any power `1 + e`, `e > 0`.
This is the arithmetic step of the covering argument; no template count or
entropy conclusion is asserted here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 9.4, `08-scanner.tex`, lines 656–664, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Finite side budgets imply an arbitrary positive-exponent dyadic moment bound.
The weights may be real; only the below-cap budget must be nonnegative.
Source: Lemma 9.4, finite geometric summation of the covering counts. -/
theorem sum_weighted_dyadic_rpow_le (a : ℕ → ℝ) (K : ℕ) {e A B : ℝ}
    (he : 0 < e) (hB : 0 ≤ B)
    (hcap : (2 : ℝ) ^ K * a K ≤ A)
    (hsmall : ∀ k < K, (2 : ℝ) ^ k * a k ≤ B) :
    (∑ k ∈ Finset.range (K + 1), a k * ((2 : ℝ) ^ k) ^ (1 + e)) ≤
      (A + B / ((2 : ℝ) ^ e - 1)) * ((2 : ℝ) ^ K) ^ e := by
  have hfactor (k : ℕ) : a k * ((2 : ℝ) ^ k) ^ (1 + e) =
      ((2 : ℝ) ^ k * a k) * ((2 : ℝ) ^ k) ^ e := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
    ring
  have htwo : 1 < (2 : ℝ) ^ e := Real.one_lt_rpow (by norm_num) he
  have hgeom : (∑ k ∈ Finset.range K, ((2 : ℝ) ^ k) ^ e) ≤
      ((2 : ℝ) ^ K) ^ e / ((2 : ℝ) ^ e - 1) := by
    simp_rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    rw [geom_sum_eq (ne_of_gt htwo)]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  rw [Finset.sum_range_succ]
  calc
    _ ≤ (∑ k ∈ Finset.range K, B * ((2 : ℝ) ^ k) ^ e) +
        A * ((2 : ℝ) ^ K) ^ e := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro k hk
        rw [hfactor]
        exact mul_le_mul_of_nonneg_right (hsmall k (Finset.mem_range.mp hk))
          (Real.rpow_nonneg (by positivity) _)
      · rw [hfactor]
        exact mul_le_mul_of_nonneg_right hcap (Real.rpow_nonneg (by positivity) _)
    _ = B * (∑ k ∈ Finset.range K, ((2 : ℝ) ^ k) ^ e) +
        A * ((2 : ℝ) ^ K) ^ e := by rw [Finset.mul_sum]
    _ ≤ B * (((2 : ℝ) ^ K) ^ e / ((2 : ℝ) ^ e - 1)) +
        A * ((2 : ℝ) ^ K) ^ e :=
      add_le_add (mul_le_mul_of_nonneg_left hgeom hB) le_rfl
    _ = _ := by ring

end TNLean.PEPS.AreaLaw.Geometry
