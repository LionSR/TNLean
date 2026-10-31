/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.OptimizedRankScale

/-!
# Logarithmic costs of the selected AKLV rank budgets

Quadratic degree bounds give linear rank exponents at the appropriate
window scale. The logarithmic estimates keep the initial contribution and
the fourth-root accuracy contribution separate.

Source: AKLV, arXiv:1301.1162v1, lines 1503--1517.
-/

open Real

namespace TNLean.MPS.AreaLaw

/-- A quadratic degree bound gives a linear exponent in the sharp rank formula. -/
theorem aklv_rank_exponent_le_of_degree_le_square {ell s n : ℕ}
    (hn : 1 ≤ n) (hns : n ≤ s) (hell : ell ≤ 66 * n ^ 2) :
    ell / s + Nat.sqrt ell + 1 ≤ 76 * n := by
  have hs : 0 < s := by omega
  have hdiv : ell / s ≤ 66 * n := by
    have hbound : ell ≤ (66 * n) * s := by nlinarith only [hell, hns]
    have h := Nat.div_le_div_right hbound (c := s)
    rwa [Nat.mul_div_cancel _ hs] at h
  have hroot : Nat.sqrt ell ≤ 9 * n := by
    have hbound : ell ≤ (9 * n) ^ 2 := by nlinarith only [hell]
    have h := Nat.sqrt_le_sqrt hbound
    rwa [Nat.sqrt_eq'] at h
  omega

/-- At the initial-width scale the extra logarithmic rank cost is absorbed
by a universal multiple of the actual initial logarithmic rank. -/
theorem aklv_log_rank_le_initial_cost {q n s ell : ℕ} (hq : 2 ≤ q)
    (hn : 1 ≤ n) (hns : n ≤ s) (hell : ell ≤ 66 * n ^ 2) :
    log (((q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1)) : ℕ) : ℝ) ≤
      10000 * log (((q * (n ^ 2 + 1)) ^ (32 * (2 * n + 1)) : ℕ) : ℝ) := by
  let b := q * (n ^ 2 + 1)
  let c := q * (ell + 1)
  have hb2 : 2 ≤ b := by dsimp only [b]; nlinarith
  have hc1 : 1 ≤ c := by dsimp only [c]; nlinarith
  have hb : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hc : 0 < (c : ℝ) := by exact_mod_cast (show 0 < c by omega)
  have hlog2 : (1 : ℝ) / 2 ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hLb : (1 : ℝ) / 2 ≤ log (b : ℝ) :=
    hlog2.trans (log_le_log (by norm_num) (by exact_mod_cast hb2))
  have hLc : 0 ≤ log (c : ℝ) := log_nonneg (by exact_mod_cast hc1)
  have hcb : c ≤ 67 * b := by
    dsimp only [b, c]
    nlinarith only [Nat.mul_le_mul_left q hell]
  have hbase : log (c : ℝ) ≤ 135 * log (b : ℝ) := by
    have h := log_le_log hc (show (c : ℝ) ≤ 67 * (b : ℝ) by exact_mod_cast hcb)
    rw [log_mul (by norm_num : (67 : ℝ) ≠ 0) (ne_of_gt hb)] at h
    have h67 : log (67 : ℝ) ≤ 67 :=
      (log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    linarith
  have hE : ((32 * (ell / s + Nat.sqrt ell + 1) : ℕ) : ℝ) ≤ 2432 * (n : ℝ) := by
    have h : 32 * (ell / s + Nat.sqrt ell + 1) ≤ 2432 * n := by
      nlinarith only [Nat.mul_le_mul_left 32
        (aklv_rank_exponent_le_of_degree_le_square hn hns hell)]
    exact_mod_cast h
  rw [Nat.cast_pow, log_pow, Nat.cast_pow, log_pow]
  change _ * log (c : ℝ) ≤ 10000 * (_ * log (b : ℝ))
  have hfirst := mul_le_mul_of_nonneg_right hE hLc
  have hsecond := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 2432 * (n : ℝ) by positivity)
  push_cast at hfirst hsecond ⊢
  nlinarith [mul_nonneg (Nat.cast_nonneg n) (show 0 ≤ log (b : ℝ) by linarith)]

/-- At the fourth-root scale, the logarithmic filter rank is linear in
that scale up to the explicit logarithmic base factors. -/
theorem aklv_log_rank_le_accuracy_cost {q n s ell : ℕ} {z : ℝ} (hq : 2 ≤ q)
    (hn : 1 ≤ n) (hns : n ≤ s) (hell : ell ≤ 66 * n ^ 2)
    (hz : 1 ≤ z) (hnz : (n : ℝ) ≤ z + 1) :
    log (((q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1)) : ℕ) : ℝ) ≤
      400000 * (n : ℝ) * (1 + log (q : ℝ) + log (z + 1)) := by
  let c := q * (ell + 1)
  let V := 1 + log (q : ℝ) + log (z + 1)
  have hc1 : 1 ≤ c := by dsimp only [c]; nlinarith
  have hc : 0 < (c : ℝ) := by exact_mod_cast (show 0 < c by omega)
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqlog : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hZ : 0 < z + 1 := by linarith
  have hZlog : 0 ≤ log (z + 1) := log_nonneg (by linarith)
  have hV : 0 ≤ V := by dsimp only [V]; linarith
  have hcnat : c ≤ 67 * q * n ^ 2 := by
    dsimp only [c]
    nlinarith only [Nat.mul_le_mul_left q hell,
      Nat.mul_le_mul_left q (one_le_pow₀ hn : 1 ≤ n ^ 2)]
  have hcR : (c : ℝ) ≤ 67 * (q : ℝ) * (z + 1) ^ 2 := by
    have hnat : (c : ℝ) ≤ 67 * (q : ℝ) * (n : ℝ) ^ 2 := by exact_mod_cast hcnat
    exact hnat.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg n) hnz 2) (by positivity))
  have hlog : log (c : ℝ) ≤ log 67 + log (q : ℝ) + 2 * log (z + 1) := by
    have h := log_le_log hc hcR
    rw [log_mul (by positivity) (by positivity),
      log_mul (by norm_num : (67 : ℝ) ≠ 0) (ne_of_gt hqpos), log_pow] at h
    simpa only [Nat.cast_ofNat] using h
  have hbase : log (c : ℝ) ≤ 134 * V := by
    have h67 : log (67 : ℝ) ≤ 67 :=
      (log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    dsimp only [V]
    linarith
  have hLc : 0 ≤ log (c : ℝ) := log_nonneg (by exact_mod_cast hc1)
  have hE : ((32 * (ell / s + Nat.sqrt ell + 1) : ℕ) : ℝ) ≤ 2432 * (n : ℝ) := by
    have h : 32 * (ell / s + Nat.sqrt ell + 1) ≤ 2432 * n := by
      nlinarith only [Nat.mul_le_mul_left 32
        (aklv_rank_exponent_le_of_degree_le_square hn hns hell)]
    exact_mod_cast h
  rw [Nat.cast_pow, log_pow]
  change _ * log (c : ℝ) ≤ 400000 * (n : ℝ) * V
  have hfirst := mul_le_mul_of_nonneg_right hE hLc
  have hsecond := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 2432 * (n : ℝ) by positivity)
  push_cast at hfirst hsecond ⊢
  nlinarith [mul_nonneg (Nat.cast_nonneg n) hV]

end TNLean.MPS.AreaLaw
