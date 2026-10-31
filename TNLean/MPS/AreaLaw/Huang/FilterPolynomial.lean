/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.FilterGrowth

/-!
# Uniform polynomial count and rank bounds for the finite Gaussian filter

For fixed local dimension, positive gap and positive precision parameter, one polynomial
with natural degree bounds the energy count, sample count, simultaneous rank budget and
their product at every chain length. Constants are chosen before length. These are
conservative existence estimates for Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19;
no sharper printed quantitative bound is asserted.
-/

namespace TNLean.MPS.AreaLaw

/-- The energy and Gaussian sample counts have uniform polynomial degrees two and three.
Supporting count estimates for Huang, Section 5.4, Lemmas 18--19. -/
theorem exists_huangFilter_count_polynomials {c Delta : ℝ}
    (hc : 0 < c) (hDelta : 0 < Delta) :
    ∃ E S : ℝ, 1 ≤ E ∧ 1 ≤ S ∧ ∀ L : ℕ,
      (huangEnergyCount c Delta L : ℝ) ≤ E * ((L : ℝ) + 1) ^ 2 ∧
      (huangFilterSampleCount c Delta L : ℝ) ≤ S * ((L : ℝ) + 1) ^ 3 := by
  obtain ⟨K, A, B, hK, hA, hB, hparams⟩ := exists_huangFilter_log_bounds hc hDelta
  let E := 2 * A / Delta + 2
  let S := 4 * B * K + 3
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hE : 1 ≤ E := by
    have : 0 ≤ 2 * A / Delta := by positivity
    dsimp only [E]
    linarith
  have hS : 1 ≤ S := by
    have : 0 ≤ 4 * B * K := by positivity
    dsimp only [S]
    linarith
  refine ⟨E, S, hE, hS, ?_⟩
  intro L
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hL1 : 0 < (L : ℝ) + 1 := by positivity
  have hlog : Real.log ((L : ℝ) + 1) + 1 ≤ (L : ℝ) + 1 := by
    linarith [Real.log_le_sub_one_of_pos hL1]
  have hscale : huangFilterScale c L + 1 ≤ A * ((L : ℝ) + 1) :=
    (hparams L).2.2.1.trans (mul_le_mul_of_nonneg_left hlog hA.le)
  have htime : huangFilterTime c Delta L ≤ B * ((L : ℝ) + 1) :=
    (hparams L).2.2.2.trans (mul_le_mul_of_nonneg_left hlog hB.le)
  have hη := huangFilterEta_bounds hc L
  have hηpos := hη.1
  have hT := huangFilterTime_pos hc hDelta L
  have hscale0 : 0 ≤ huangFilterScale c L + 1 := by
    linarith [huangFilterScale_ge_eight hc L]
  constructor
  · have hcount := timeMeshCount_le hL (huangEnergyMesh_bounds hc hDelta L).1
    change (huangEnergyCount c Delta L : ℝ) ≤ _ at hcount
    calc
      _ ≤ 2 * (L : ℝ) / huangEnergyMesh c Delta L + 2 := hcount
      _ = 2 * (L : ℝ) * (huangFilterScale c L + 1) / Delta + 2 := by
        dsimp only [huangEnergyMesh]
        rw [div_div_eq_mul_div]
      _ ≤ 2 * ((L : ℝ) + 1) * (A * ((L : ℝ) + 1)) / Delta + 2 := by
        gcongr
        linarith
      _ = (2 * A / Delta) * ((L : ℝ) + 1) ^ 2 + 2 := by ring
      _ ≤ E * ((L : ℝ) + 1) ^ 2 := by
        dsimp only [E]
        nlinarith
  · have hx : 0 ≤ 2 * huangFilterTime c Delta L * (2 * (L : ℝ) + 1) /
        huangFilterEta c L + 2 := by positivity
    have hceil := (Nat.ceil_lt_add_one hx).le
    change (huangFilterSampleCount c Delta L : ℝ) ≤ _ at hceil
    calc
      _ ≤ 2 * huangFilterTime c Delta L * (2 * (L : ℝ) + 1) /
          huangFilterEta c L + 3 := by linarith only [hceil]
      _ = 2 * huangFilterTime c Delta L * (2 * (L : ℝ) + 1) *
          (1 / huangFilterEta c L) + 3 := by ring
      _ ≤ 2 * (B * ((L : ℝ) + 1)) * (2 * ((L : ℝ) + 1)) *
          (K * ((L : ℝ) + 1)) + 3 := by
        gcongr
        · linarith
        · exact (hparams L).1
      _ = 4 * B * K * ((L : ℝ) + 1) ^ 3 + 3 := by ring
      _ ≤ S * ((L : ℝ) + 1) ^ 3 := by
        dsimp only [S]
        have hpow : 1 ≤ ((L : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
        nlinarith only [hpow]

/-- One natural-degree polynomial bounds all actual finite-filter counts and ranks,
uniformly in length. Its constants depend on fixed `q`, `Delta`, `c` only.
This is a conservative polynomial existence bound supporting Huang, Section 5.4,
Lemmas 18--19, rather than the printed sharper gap dependence. -/
theorem exists_huangFilter_uniform_polynomial {q : ℕ} (hq : 1 ≤ q) {c Delta : ℝ}
    (hc : 0 < c) (hDelta : 0 < Delta) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ L : ℕ,
      (huangEnergyCount c Delta L : ℝ) ≤ C * ((L : ℝ) + 1) ^ d ∧
      (huangFilterSampleCount c Delta L : ℝ) ≤ C * ((L : ℝ) + 1) ^ d ∧
      (huangFilterRankBound q c Delta L : ℝ) ≤ C * ((L : ℝ) + 1) ^ d ∧
      ((huangEnergyCount c Delta L * huangFilterRankBound q c Delta L : ℕ) : ℝ) ≤
        C * ((L : ℝ) + 1) ^ d := by
  obtain ⟨E, S, hE, hS, hcounts⟩ := exists_huangFilter_count_polynomials hc hDelta
  obtain ⟨d, hbond⟩ := exists_huangFilter_bond_polynomial hq hc hDelta
  let C := E * S * Real.exp d
  have hEpos : 0 < E := lt_of_lt_of_le (by norm_num) hE
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hS
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, d + 5, ?_⟩
  intro L
  have hη := huangFilterEta_bounds hc L
  have hηpos := hη.1
  have hT := huangFilterTime_pos hc hDelta L
  have henergy : 1 ≤ huangEnergyCount c Delta L := by
    dsimp only [huangEnergyCount, timeMeshCount]
    omega
  have hsample : 1 ≤ huangFilterSampleCount c Delta L := by
    dsimp only [huangFilterSampleCount]
    have hx : 0 < 2 * huangFilterTime c Delta L * (2 * (L : ℝ) + 1) /
        huangFilterEta c L + 2 := by positivity
    exact Nat.ceil_pos.mpr hx
  have hqpow : 1 ≤ q ^ (8 * chainPropagationRadius L
      (huangFilterTime c Delta L) (huangFilterEta c L) + 8) := one_le_pow₀ hq
  have hsampleRank : huangFilterSampleCount c Delta L ≤ huangFilterRankBound q c Delta L := by
    dsimp only [huangFilterRankBound]
    simpa only [mul_one] using Nat.mul_le_mul_left (huangFilterSampleCount c Delta L) hqpow
  have hrank : 1 ≤ huangFilterRankBound q c Delta L := hsample.trans hsampleRank
  have hproduct :
      ((huangEnergyCount c Delta L * huangFilterRankBound q c Delta L : ℕ) : ℝ) ≤
        C * ((L : ℝ) + 1) ^ (d + 5) := by
    calc
      _ = (huangEnergyCount c Delta L : ℝ) * ((huangFilterSampleCount c Delta L : ℝ) *
          ((q ^ (8 * chainPropagationRadius L (huangFilterTime c Delta L)
            (huangFilterEta c L) + 8) : ℕ) : ℝ)) := by
        simp only [huangFilterRankBound, Nat.cast_mul]
      _ ≤ (E * ((L : ℝ) + 1) ^ 2) * ((S * ((L : ℝ) + 1) ^ 3) *
          (Real.exp d * ((L : ℝ) + 1) ^ d)) := by
        gcongr
        · exact (hcounts L).1
        · exact (hcounts L).2
        · exact hbond L
      _ = C * ((L : ℝ) + 1) ^ (d + 5) := by
        dsimp only [C]
        rw [pow_add]
        ring
  have hrankProduct : huangFilterRankBound q c Delta L ≤
      huangEnergyCount c Delta L * huangFilterRankBound q c Delta L := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (huangFilterRankBound q c Delta L) henergy
  have henergyProduct : huangEnergyCount c Delta L ≤
      huangEnergyCount c Delta L * huangFilterRankBound q c Delta L := by
    simpa only [mul_one] using Nat.mul_le_mul_left (huangEnergyCount c Delta L) hrank
  refine ⟨?_, ?_, ?_, hproduct⟩
  · apply le_trans _ hproduct
    exact_mod_cast henergyProduct
  · apply le_trans _ hproduct
    exact_mod_cast hsampleRank.trans hrankProduct
  · apply le_trans _ hproduct
    exact_mod_cast hrankProduct

/-- The uniform bound can be chosen with a natural coefficient as well as a natural
degree. This supplies integer cardinality and bond budgets for Huang, Section 5.4,
Lemmas 18--19, uniformly before the chain length is chosen. -/
theorem exists_huangFilter_uniform_nat_polynomial {q : ℕ} (hq : 1 ≤ q) {c Delta : ℝ}
    (hc : 0 < c) (hDelta : 0 < Delta) :
    ∃ C d : ℕ, 1 ≤ C ∧ ∀ L : ℕ,
      huangEnergyCount c Delta L ≤ C * (L + 1) ^ d ∧
      huangFilterSampleCount c Delta L ≤ C * (L + 1) ^ d ∧
      huangFilterRankBound q c Delta L ≤ C * (L + 1) ^ d ∧
      huangEnergyCount c Delta L * huangFilterRankBound q c Delta L ≤ C * (L + 1) ^ d := by
  obtain ⟨C, hC, d, hbounds⟩ := exists_huangFilter_uniform_polynomial hq hc hDelta
  refine ⟨⌈C⌉₊, d, Nat.ceil_pos.mpr hC, ?_⟩
  intro L
  have hceil : C * ((L : ℝ) + 1) ^ d ≤ (⌈C⌉₊ : ℝ) * ((L : ℝ) + 1) ^ d :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity)
  obtain ⟨hE, hS, hR, hP⟩ := hbounds L
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast hE.trans hceil
  · exact_mod_cast hS.trans hceil
  · exact_mod_cast hR.trans hceil
  · exact_mod_cast hP.trans hceil

end TNLean.MPS.AreaLaw
