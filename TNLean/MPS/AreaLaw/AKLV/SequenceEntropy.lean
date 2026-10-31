/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.SequenceEntropyParameters

/-!
# Finite entropy summation for the actual AKLV rank product

The actual product ranks grow at least geometrically. Their logarithmic
increments are the logarithms of the actual next filter ranks. The generic
finite rank-tail entropy inequality and finite dyadic moments therefore
bound entropy by a universal multiple of the initial logarithmic rank.

Source: AKLV, arXiv:1301.1162v1, lines 1059--1075. The multiplicative rank
product is retained, correcting the additive rank summary at line 1053.
-/

open Real
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- The actual product ranks are nondecreasing and dominate a geometric
schedule. This also supplies a finite covering cutoff in any dimension. -/
theorem aklvSequenceRankBound_growth {q : ℕ} (hq : 2 ≤ q) (g : ℝ) (s : ℕ) :
    (∀ i, aklvSequenceRankBound q g s i ≤ aklvSequenceRankBound q g s (i + 1)) ∧
      ∀ i, 2 ^ (i + 1) ≤ aklvSequenceRankBound q g s i := by
  have hF := aklvSequenceFilterRank_two_le hq g s
  have hbase : 2 ≤ q * (s ^ 2 + 1) := by nlinarith
  have hR0 : 2 ≤ aklvSequenceRankBound q g s 0 := by
    rw [(aklvSequenceRankBound_zero_succ q g s 0).1]
    exact hbase.trans (by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ q * (s ^ 2 + 1))
        (by change 0 < 32 * (2 * s + 1); positivity : 1 ≤ 32 * (2 * s + 1)))
  constructor
  · intro i
    rw [(aklvSequenceRankBound_zero_succ q g s i).2]
    exact Nat.le_mul_of_pos_left _ (by have := hF (i + 1); omega)
  · intro i
    induction i with
    | zero => simpa using hR0
    | succ i ih =>
      rw [(aklvSequenceRankBound_zero_succ q g s i).2, pow_succ]
      convert Nat.mul_le_mul (hF (i + 1)) ih using 1
      ring

/-- Dyadic tails at the actual product ranks give entropy bounded by the
initial logarithmic rank. The probability family need not be decreasing. -/
theorem probabilityEntropy_le_aklvSequenceRankBound {N q s : ℕ}
    (hq : 2 ≤ q) {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hs : 1 ≤ s)
    (hgap : 1 / g ≤ (s : ℝ))
    (hT : aklvLogarithmicThreshold g ≤ 1040 * (s : ℝ))
    (p : Fin N → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (htail : ∀ i < N, (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦
      aklvSequenceRankBound q g s i ≤ a.val), p a) ≤ aklvSequenceWeight i / 16) :
    Entropy.probabilityEntropy p ≤ 300000 * log (aklvSequenceRankBound q g s 0 : ℝ) := by
  let R := aklvSequenceRankBound q g s
  let L0 := log (R 0 : ℝ)
  obtain ⟨hmono, hlarge⟩ := aklvSequenceRankBound_growth hq g s
  have hRpos (i : ℕ) : 0 < (R i : ℝ) := by
    have h := hlarge i
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 2 ^ (i + 1)) h)
  have hlog2 : log 2 ≤ L0 := log_le_log (by norm_num)
    (by exact_mod_cast (by simpa using hlarge 0 : 2 ≤ R 0))
  have hL0 : 0 ≤ L0 := (log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hlog2
  have hratio (i : ℕ) : log ((R (i + 1) : ℝ) / (R i : ℝ)) =
      log (aklvSequenceFilterRank q g s (i + 1) : ℝ) := by
    have hF : 0 < (aklvSequenceFilterRank q g s (i + 1) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2)
        (aklvSequenceFilterRank_two_le hq g s (i + 1)))
    rw [log_div (hRpos (i + 1)).ne' (hRpos i).ne']
    change log (aklvSequenceRankBound q g s (i + 1) : ℝ) - _ = _
    rw [(aklvSequenceRankBound_zero_succ q g s i).2, Nat.cast_mul,
      log_mul hF.ne' (hRpos i).ne']
    ring
  have hcost (i : ℕ) : log ((R (i + 1) : ℝ) / (R i : ℝ)) ≤
      200000 * ((i : ℝ) + 2) ^ 2 * L0 := by
    rw [hratio]
    have h := aklvSequenceFilterRank_log_le_initial_rank hq hg hg1 hs hgap hT (i + 1)
    rw [← (aklvSequenceRankBound_zero_succ q g s 0).1] at h
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  have hmass : (∑ i ∈ Finset.range N, aklvSequenceWeight i / 16) ≤ 1 / 8 := by
    have h := sum_quadratic_div_dyadic_le 0 0 1
      (by norm_num) (by norm_num) (by norm_num) N
    norm_num only [zero_mul, zero_add] at h
    calc
      _ = (1 / 8 : ℝ) * ∑ i ∈ Finset.range N, 1 / (2 : ℝ) ^ (i + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [aklvSequenceWeight, pow_succ]
        ring
      _ ≤ (1 / 8 : ℝ) * 1 := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by norm_num
  have hmoment := sum_quadratic_div_dyadic_le 1 4 4
    (by norm_num) (by norm_num) (by norm_num) N
  norm_num only [one_mul] at hmoment
  have hweighted : (∑ i ∈ Finset.range N,
      aklvSequenceWeight i / 16 * log ((R (i + 1) : ℝ) / (R i : ℝ))) ≤ 275000 * L0 := by
    calc
      _ ≤ ∑ i ∈ Finset.range N,
          aklvSequenceWeight i / 16 * (200000 * ((i : ℝ) + 2) ^ 2 * L0) := by
        exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hcost i)
          (div_nonneg (aklvSequenceWeight_pos_le_one i).1.le (by norm_num))
      _ = (25000 * L0) * ∑ i ∈ Finset.range N,
          ((i : ℝ) ^ 2 + 4 * (i : ℝ) + 4) / (2 : ℝ) ^ (i + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [aklvSequenceWeight, pow_succ]
        ring
      _ ≤ (25000 * L0) * 11 :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = _ := by ring
  have hraw := Entropy.probabilityEntropy_le_of_rankTailBounds (M := N)
    p R (fun i ↦ aklvSequenceWeight i / 16) hp hsum
    (lt_of_lt_of_le (by decide : 0 < 2) (by simpa using hlarge 0))
    (fun i _ ↦ hmono i)
    ((show N ≤ 2 ^ N from Nat.lt_two_pow_self.le).trans ((Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.le_succ N)).trans (hlarge N))) htail
  have hlog2pos : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hmiddle := mul_le_mul_of_nonneg_left (add_le_add_left hmass 1) hlog2pos
  change Entropy.probabilityEntropy p ≤ 300000 * L0
  change Entropy.probabilityEntropy p ≤ L0 + _ + _ at hraw
  nlinarith only [hraw, hweighted, hmiddle, hlog2, hL0]

end TNLean.MPS.AreaLaw
