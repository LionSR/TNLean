/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ChebyshevAGSP.SequenceParameters
import TNLean.MPS.AreaLaw.ChebyshevAGSP.OptimizedInitialScale
import QICLean.Entropy.Classical.ProbabilityEntropyRankTails

/-!
# Logarithmic rank costs for the actual AKLV sequence

The selected square-root degrees and actual polynomial rank bounds have
quadratic logarithmic costs in the sequence index, relative to the actual
initial logarithmic rank. Dyadic weighting therefore gives a uniform
finite cost. No filter or rank estimate is supplied as a hypothesis.

Source: AKLV, arXiv:1301.1162v1, Lemma `l:5` and entropy summation,
lines 1003--1075. The coarse estimates here serve the entropy summation;
the separate optimized accuracy-dependent approximation is unchanged.

## Finite entropy summation for the actual AKLV rank product

The actual product ranks grow at least geometrically. Their logarithmic
increments are the logarithms of the actual next filter ranks. The generic
finite rank-tail entropy inequality and finite dyadic moments therefore
bound entropy by a universal multiple of the initial logarithmic rank.

Source: AKLV, arXiv:1301.1162v1, lines 1059--1075. The multiplicative rank
product is retained, correcting the additive rank summary at line 1053.
-/

section

open Real
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- The actual square-root degree is at most linear in the index at any
initial width dominating the inverse gap and the initial threshold. -/
theorem aklvSequenceDegree_le_linear {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    {s : ℕ} (hs : 1 ≤ s) (hgap : 1 / g ≤ (s : ℝ))
    (hT : aklvLogarithmicThreshold g ≤ 1040 * (s : ℝ)) (j : ℕ) :
    1 ≤ aklvSequenceDegree g s j ∧ aklvSequenceDegree g s j ≤ 240 * s * (j + 1) := by
  let W := 2 * aklvSequenceThreshold g j + s
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hWpos : 0 < W := by
    have ht := aklvSequenceThreshold_pos hg hg1 j
    dsimp only [W]
    positivity
  have hW : W ≤ 2113 * (s : ℝ) * ((j : ℝ) + 1) := by
    dsimp only [W, aklvSequenceThreshold]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsR) hj,
      mul_le_mul_of_nonneg_left hlog2 hj]
  have hWG : W / g ≤ 2113 * (s : ℝ) ^ 2 * ((j : ℝ) + 1) := by
    calc
      _ ≤ 2113 * (s : ℝ) * ((j : ℝ) + 1) / g := div_le_div_of_nonneg_right hW hg.le
      _ = (2113 * (s : ℝ) * ((j : ℝ) + 1)) * (1 / g) := by ring
      _ ≤ (2113 * (s : ℝ) * ((j : ℝ) + 1)) * (s : ℝ) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = _ := by ring
  have hroot : sqrt (W / g) ≤ 46 * (s : ℝ) * ((j : ℝ) + 1) := by
    calc
      _ ≤ sqrt ((46 * (s : ℝ) * ((j : ℝ) + 1)) ^ 2) := sqrt_le_sqrt (by
        calc
          _ ≤ 2113 * (s : ℝ) ^ 2 * ((j : ℝ) + 1) := hWG
          _ ≤ 2116 * (s : ℝ) ^ 2 * ((j : ℝ) + 1) ^ 2 := by
            gcongr
            · norm_num
            · nlinarith
          _ = _ := by ring)
      _ = _ := sqrt_sq (by positivity)
  have hdegree := (aklvSequenceDegree_bounds g s j).1
  have hscaledpos : 0 < 5 * sqrt (W / g) := by positivity
  have hdegreepos : 0 < (aklvSequenceDegree g s j : ℝ) := hscaledpos.trans_le hdegree
  have hdegreeNat : 0 < aklvSequenceDegree g s j := by exact_mod_cast hdegreepos
  refine ⟨hdegreeNat, ?_⟩
  apply Nat.ceil_le.mpr
  push_cast
  change 5 * sqrt (W / g) ≤ 240 * (s : ℝ) * ((j : ℝ) + 1)
  nlinarith [mul_nonneg (Nat.cast_nonneg s) (show 0 ≤ (j : ℝ) + 1 by positivity)]

/-- Every actual filter rank dominates the local dimension. -/
theorem aklvSequenceFilterRank_two_le {q : ℕ} (hq : 2 ≤ q)
    (g : ℝ) (s j : ℕ) : 2 ≤ aklvSequenceFilterRank q g s j := by
  let ell := aklvSequenceDegree g s j
  have hb : 2 ≤ q * (ell + 1) := by nlinarith
  exact hb.trans (by
    change q * (ell + 1) ≤ (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ q * (ell + 1))
      (by change 0 < 32 * (ell / s + Nat.sqrt ell + 1); positivity :
        1 ≤ 32 * (ell / s + Nat.sqrt ell + 1)))

/-- The logarithmic cost of each actual filter is quadratic in its index,
relative to the actual initial logarithmic rank. -/
theorem aklvSequenceFilterRank_log_le_initial_rank {q s : ℕ} (hq : 2 ≤ q)
    {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hs : 1 ≤ s)
    (hgap : 1 / g ≤ (s : ℝ))
    (hT : aklvLogarithmicThreshold g ≤ 1040 * (s : ℝ)) (j : ℕ) :
    log (aklvSequenceFilterRank q g s j : ℝ) ≤
      200000 * ((j : ℝ) + 1) ^ 2 *
        log (((q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) : ℕ) : ℝ) := by
  let ell := aklvSequenceDegree g s j
  let b := q * (s ^ 2 + 1)
  let c := q * (ell + 1)
  obtain ⟨hell1, hell⟩ := aklvSequenceDegree_le_linear hg hg1 hs hgap hT j
  change 1 ≤ ell at hell1
  change ell ≤ 240 * s * (j + 1) at hell
  have hb2 : 2 ≤ b := by dsimp only [b]; nlinarith
  have hc1 : 1 ≤ c := by dsimp only [c]; nlinarith
  have hb : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hc : 0 < (c : ℝ) := by exact_mod_cast (show 0 < c by omega)
  have hlog2 : (1 : ℝ) / 2 ≤ log 2 := by linarith only [log_two_gt_d9]
  have hLb : (1 : ℝ) / 2 ≤ log (b : ℝ) :=
    hlog2.trans (log_le_log (by norm_num) (by exact_mod_cast hb2))
  have hLc : 0 ≤ log (c : ℝ) := log_nonneg (by exact_mod_cast hc1)
  have hds : ell + 1 ≤ 241 * (s ^ 2 + 1) * (j + 1) := by
    have hsq : s ≤ s ^ 2 + 1 := by nlinarith
    have h := Nat.mul_le_mul_right (j + 1) hsq
    have hp : 1 ≤ (s ^ 2 + 1) * (j + 1) := by
      change 0 < (s ^ 2 + 1) * (j + 1)
      positivity
    nlinarith only [hell, h, hp]
  have hcb : c ≤ 241 * (j + 1) * b := by
    have h := Nat.mul_le_mul_left q hds
    dsimp only [b, c]
    nlinarith only [h]
  have hbase : log (c : ℝ) ≤ 485 * ((j : ℝ) + 1) * log (b : ℝ) := by
    have h := log_le_log hc (show (c : ℝ) ≤ 241 * ((j : ℝ) + 1) * (b : ℝ) by
      exact_mod_cast hcb)
    rw [log_mul (by positivity) (ne_of_gt hb),
      log_mul (by norm_num : (241 : ℝ) ≠ 0) (by positivity)] at h
    have h241 : log (241 : ℝ) ≤ 241 :=
      (log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have hjlog : log ((j : ℝ) + 1) ≤ (j : ℝ) + 1 :=
      (log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hLb (show 0 ≤ (j : ℝ) + 1 by positivity)]
  have hE : ((32 * (ell / s + Nat.sqrt ell + 1) : ℕ) : ℝ) ≤
      23040 * (s : ℝ) * ((j : ℝ) + 1) := by
    have hdiv : ell / s ≤ ell := Nat.div_le_self _ _
    have hroot : Nat.sqrt ell ≤ ell := Nat.sqrt_le_self _
    have h : 32 * (ell / s + Nat.sqrt ell + 1) ≤ 23040 * s * (j + 1) := by
      nlinarith only [hdiv, hroot, hell1, hell]
    exact_mod_cast h
  have hfirst := mul_le_mul_of_nonneg_right hE hLc
  have hsecond := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ 23040 * (s : ℝ) * ((j : ℝ) + 1) by positivity)
  unfold aklvSequenceFilterRank
  rw [Nat.cast_pow, log_pow, Nat.cast_pow, log_pow]
  change _ * log (c : ℝ) ≤ 200000 * ((j : ℝ) + 1) ^ 2 * (_ * log (b : ℝ))
  push_cast at hfirst hsecond ⊢
  have hnonneg : 0 ≤ (s : ℝ) * ((j : ℝ) + 1) ^ 2 * log (b : ℝ) := by positivity
  nlinarith only [hfirst, hsecond, hnonneg,
    mul_nonneg (show 0 ≤ ((j : ℝ) + 1) ^ 2 by positivity)
      (show 0 ≤ log (b : ℝ) by linarith)]

end TNLean.MPS.AreaLaw

end

section

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

end
