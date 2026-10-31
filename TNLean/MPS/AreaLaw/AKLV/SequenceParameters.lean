/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.PhysicalRobustness

/-!
# Thresholds and degrees for the changing-target AKLV sequence

The clipping threshold grows linearly with the index. A degree proportional
to the square root of the spectral ceiling divided by the gap makes every
squared shrinking factor at most one over 256. The error weights are dyadic.

Source: AKLV, arXiv:1301.1162v1, Lemma `l:5`, lines 1003--1052.
These explicit conservative constants serve the actual normalized-filter
recursion; the separate accuracy-dependent enlarged-window optimization is
not asserted here.
-/

open Real

namespace TNLean.MPS.AreaLaw

/-- The dyadic squared-error weight in the changing-target sequence. -/
noncomputable def aklvSequenceWeight (i : ℕ) : ℝ := ((2 : ℝ) ^ i)⁻¹

/-- A linearly increasing threshold for the actual two clipped exteriors. -/
noncomputable def aklvSequenceThreshold (g : ℝ) (i : ℕ) : ℝ :=
  aklvLogarithmicThreshold g + 16 * (i : ℝ) * log 2

/-- Degree used to refine the preceding state at a fixed physical window. -/
noncomputable def aklvSequenceDegree (g : ℝ) (s i : ℕ) : ℕ :=
  ⌈5 * sqrt ((2 * aklvSequenceThreshold g i + s) / g)⌉₊

/-- Initial weight and the exact successive dyadic relation. -/
theorem aklvSequenceWeight_zero_succ (i : ℕ) :
    aklvSequenceWeight 0 = 1 ∧
      aklvSequenceWeight i = 2 * aklvSequenceWeight (i + 1) := by
  simp only [aklvSequenceWeight, pow_zero, inv_one, pow_succ, mul_inv_rev]
  norm_num
  ring

/-- Every error weight is positive and at most one. -/
theorem aklvSequenceWeight_pos_le_one (i : ℕ) :
    0 < aklvSequenceWeight i ∧ aklvSequenceWeight i ≤ 1 := by
  refine ⟨by unfold aklvSequenceWeight; positivity, ?_⟩
  simp only [aklvSequenceWeight, ← one_div]
  change 1 / (2 : ℝ) ^ i ≤ 1
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

/-- The chosen threshold is always above the physical logarithmic threshold. -/
theorem aklvLogarithmicThreshold_le_sequenceThreshold (g : ℝ) (i : ℕ) :
    aklvLogarithmicThreshold g ≤ aklvSequenceThreshold g i := by
  have hlog : 0 ≤ log 2 := log_nonneg (by norm_num)
  unfold aklvSequenceThreshold
  exact le_add_of_nonneg_right (by positivity)

/-- Positive gaps capped at one give positive thresholds. -/
theorem aklvSequenceThreshold_pos {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (i : ℕ) :
    0 < aklvSequenceThreshold g i := by
  have hlog : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hT : 0 < aklvLogarithmicThreshold g := by
    unfold aklvLogarithmicThreshold
    positivity
  exact hT.trans_le (aklvLogarithmicThreshold_le_sequenceThreshold g i)

/-- The actual clipped-target squared error decays at least dyadically. -/
theorem exp_neg_sequenceThreshold_div_le {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (i : ℕ) :
    exp (-aklvSequenceThreshold g i / 16) ≤ aklvSequenceWeight i := by
  have hT : 0 ≤ aklvLogarithmicThreshold g := by
    have hlog : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
    unfold aklvLogarithmicThreshold
    positivity
  have heq : -aklvSequenceThreshold g i / 16 =
      -aklvLogarithmicThreshold g / 16 - (i : ℝ) * log 2 := by
    unfold aklvSequenceThreshold
    ring
  rw [heq, exp_sub, exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
  have hexp : exp (-aklvLogarithmicThreshold g / 16) ≤ 1 :=
    exp_le_one_iff.mpr (by linarith)
  simpa only [aklvSequenceWeight, one_div] using
    div_le_div_of_nonneg_right hexp (show 0 ≤ (2 : ℝ) ^ i by positivity)

/-- The rounded degree has the claimed square-root scale. -/
theorem aklvSequenceDegree_bounds (g : ℝ) (s i : ℕ) :
    5 * sqrt ((2 * aklvSequenceThreshold g i + s) / g) ≤
        (aklvSequenceDegree g s i : ℝ) ∧
      (aklvSequenceDegree g s i : ℝ) <
        5 * sqrt ((2 * aklvSequenceThreshold g i + s) / g) + 1 := by
  have hnonneg : 0 ≤ 5 * sqrt ((2 * aklvSequenceThreshold g i + s) / g) := by positivity
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one hnonneg⟩

/-- The actual squared Chebyshev shrinking factor is uniformly small at
these rounded degrees, independently of the sequence index. -/
theorem aklvSequenceDegree_shrink_le {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (s i : ℕ) :
    (2 * exp (-2 * (aklvSequenceDegree g s i : ℝ) *
      sqrt ((9 * g / 10) / (2 * aklvSequenceThreshold g i + s)))) ^ 2 ≤ 1 / 256 := by
  let W := 2 * aklvSequenceThreshold g i + s
  let ell := aklvSequenceDegree g s i
  have hW : 0 < W := by
    have ht := aklvSequenceThreshold_pos hg hg1 i
    dsimp only [W]
    positivity
  have hproduct : sqrt (W / g) * sqrt ((9 * g / 10) / W) = sqrt (9 / 10) := by
    rw [← sqrt_mul (div_nonneg hW.le hg.le)]
    congr 1
    field_simp
  have hroot : (1 : ℝ) / 2 ≤ sqrt (9 / 10) := le_sqrt_of_sq_le (by norm_num)
  have hdegree : 5 * sqrt (W / g) ≤ (ell : ℝ) :=
    (aklvSequenceDegree_bounds g s i).1
  have hscaled : 10 ≤ 4 * (ell : ℝ) * sqrt ((9 * g / 10) / W) := by
    have hmul := mul_le_mul_of_nonneg_right hdegree (sqrt_nonneg ((9 * g / 10) / W))
    nlinarith [hproduct]
  have hexp : exp (-10) ≤ (1 : ℝ) / 1024 := by
    have htwo : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    have hten : (1024 : ℝ) ≤ exp 10 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 10
      rw [← exp_nat_mul] at hp
      norm_num at hp ⊢
      exact hp
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hten
  change (2 * exp (-2 * (ell : ℝ) * sqrt ((9 * g / 10) / W))) ^ 2 ≤ _
  calc
    _ = 4 * exp (-(4 * (ell : ℝ) * sqrt ((9 * g / 10) / W))) := by
      rw [mul_pow, ← exp_nat_mul]
      congr 2 <;> norm_num
      ring
    _ ≤ 4 * exp (-10) := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num)
    _ ≤ 1 / 256 := by linarith

/-- The sharp operator-Schmidt rank budget of a single selected filter. -/
noncomputable def aklvSequenceFilterRank (q : ℕ) (g : ℝ) (s i : ℕ) : ℕ :=
  let ell := aklvSequenceDegree g s i
  (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))

/-- The initial rank times the product of the successive actual filter budgets. -/
noncomputable def aklvSequenceRankBound (q : ℕ) (g : ℝ) (s i : ℕ) : ℕ :=
  (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) *
    ∏ j ∈ Finset.range i, aklvSequenceFilterRank q g s (j + 1)

/-- Initial and successive forms of the exact rank product. -/
theorem aklvSequenceRankBound_zero_succ (q : ℕ) (g : ℝ) (s i : ℕ) :
    aklvSequenceRankBound q g s 0 = (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) ∧
      aklvSequenceRankBound q g s (i + 1) =
        aklvSequenceFilterRank q g s (i + 1) * aklvSequenceRankBound q g s i := by
  simp only [aklvSequenceRankBound, Finset.range_zero, Finset.prod_empty, mul_one,
    Finset.prod_range_succ]
  constructor
  · trivial
  · ring

end TNLean.MPS.AreaLaw
