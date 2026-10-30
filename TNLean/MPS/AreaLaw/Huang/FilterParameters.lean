/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.GridParameters
import TNLean.MPS.AreaLaw.Huang.GaussianQuadrature

/-!
# Explicit scalar parameters for approximate-energy Gaussian filtering

The precision decreases inversely with chain length. A logarithmic Gaussian scale
suppresses the excited spectrum, and a positive time cutoff controls the Gaussian tail.
The energy mesh preserves both a half-gap estimate and a uniform ground amplitude.

These are conservative supporting choices for Huang, arXiv:1406.6355v6, Section 5.4,
equations (19)--(22) and Lemmas 18--19. No assertion of the source's sharper gap dependence
or printed constants is made.
-/

open scoped NNReal

namespace TNLean.MPS.AreaLaw

/-- Precision for the finite filter construction; Huang, Section 5.4, Lemmas 18--19. -/
noncomputable def huangFilterEta (c : ℝ) (L : ℕ) : ℝ :=
  c / (64 * (c + L + 1))

/-- A conservative logarithmic spectral scale; Huang, Section 5.4, equation (19). -/
noncomputable def huangFilterScale (c : ℝ) (L : ℕ) : ℝ :=
  8 * Real.log (1 / huangFilterEta c L) + 8

/-- Gaussian time variance for gap `Delta`; Huang, Section 5.4, equation (19). -/
noncomputable def huangFilterVariance (c Delta : ℝ) (L : ℕ) : ℝ≥0 :=
  (huangFilterScale c L / Delta ^ 2).toNNReal

/-- A time cutoff controlling the Gaussian tail; Huang, Section 5.4, equations (20)--(22). -/
noncomputable def huangFilterTime (c Delta : ℝ) (L : ℕ) : ℝ :=
  huangFilterVariance c Delta L + Real.log (2 / huangFilterEta c L) + 1

/-- Energy accuracy retaining a uniform ground amplitude; Huang, Section 5.4, Lemma 18. -/
noncomputable def huangEnergyMesh (c Delta : ℝ) (L : ℕ) : ℝ :=
  Delta / (huangFilterScale c L + 1)

/-- The constructed energy-grid cardinality; Huang, Section 5.4, Lemma 18. -/
noncomputable def huangEnergyCount (c Delta : ℝ) (L : ℕ) : ℕ :=
  timeMeshCount L (huangEnergyMesh c Delta L)

/-- A uniform upper sample count for all energy estimates of modulus at most `L`.
Huang, Section 5.4, equations (20)--(22). -/
noncomputable def huangFilterSampleCount (c Delta : ℝ) (L : ℕ) : ℕ :=
  ⌈2 * huangFilterTime c Delta L * (2 * L + 1) / huangFilterEta c L + 2⌉₊

/-- The simultaneous cut-rank budget for the finite Gaussian sum; Huang, Lemma 19. -/
noncomputable def huangFilterRankBound (q : ℕ) (c Delta : ℝ) (L : ℕ) : ℕ :=
  huangFilterSampleCount c Delta L *
    q ^ (8 * chainPropagationRadius L (huangFilterTime c Delta L) (huangFilterEta c L) + 8)

/-- The constructed precision is strictly between zero and `1/64`.
Huang, Section 5.4, supporting precision choice for Lemmas 18--19. -/
theorem huangFilterEta_bounds {c : ℝ} (hc : 0 < c) (L : ℕ) :
    0 < huangFilterEta c L ∧ huangFilterEta c L < 1 / 64 := by
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hden : 0 < 64 * (c + L + 1) := by positivity
  constructor
  · exact div_pos hc hden
  · dsimp only [huangFilterEta]
    rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 64)]
    nlinarith

/-- The logarithmic spectral scale is at least eight; Huang, Section 5.4, equation (19). -/
theorem huangFilterScale_ge_eight {c : ℝ} (hc : 0 < c) (L : ℕ) :
    8 ≤ huangFilterScale c L := by
  have hη := huangFilterEta_bounds hc L
  have hlog : 0 ≤ Real.log (1 / huangFilterEta c L) :=
    Real.log_nonneg ((one_le_div hη.1).mpr (by linarith [hη.2]))
  dsimp only [huangFilterScale]
  linarith

/-- Coercion of the positive Gaussian variance; Huang, Section 5.4, equation (19). -/
theorem huangFilterVariance_coe {c : ℝ} (hc : 0 < c) (Delta : ℝ) (L : ℕ) :
    (huangFilterVariance c Delta L : ℝ) = huangFilterScale c L / Delta ^ 2 := by
  exact Real.coe_toNNReal _
    (div_nonneg (by linarith [huangFilterScale_ge_eight hc L]) (sq_nonneg Delta))

/-- The Gaussian variance is positive for a positive gap; Huang, Section 5.4, equation (19). -/
theorem huangFilterVariance_pos {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) (L : ℕ) :
    0 < (huangFilterVariance c Delta L : ℝ) := by
  rw [huangFilterVariance_coe hc]
  exact div_pos (by linarith [huangFilterScale_ge_eight hc L]) (sq_pos_of_pos hDelta)

/-- The logarithmic cutoff contribution is positive; Huang, Section 5.4, equations (20)--(22). -/
theorem huangFilterTime_log_pos {c : ℝ} (hc : 0 < c) (L : ℕ) :
    0 < Real.log (2 / huangFilterEta c L) := by
  have hη := huangFilterEta_bounds hc L
  apply Real.log_pos
  exact (one_lt_div hη.1).mpr (by linarith [hη.2])

/-- The chosen time cutoff is positive; Huang, Section 5.4, equations (20)--(22). -/
theorem huangFilterTime_pos {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) (L : ℕ) :
    0 < huangFilterTime c Delta L := by
  dsimp only [huangFilterTime]
  linarith [huangFilterVariance_pos hc hDelta L, huangFilterTime_log_pos hc L]

/-- The Gaussian mass outside the cutoff contributes at most the chosen precision.
Huang, Section 5.4, equations (20)--(22). -/
theorem huangFilterTime_tail_le {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) (L : ℕ) :
    2 * Real.exp (-(huangFilterTime c Delta L) ^ 2 /
      (2 * (huangFilterVariance c Delta L : ℝ))) ≤ huangFilterEta c L := by
  let v := (huangFilterVariance c Delta L : ℝ)
  let s := Real.log (2 / huangFilterEta c L)
  have hv : 0 < v := huangFilterVariance_pos hc hDelta L
  have hs : 0 < s := huangFilterTime_log_pos hc L
  have hsq : 2 * v * s ≤ (v + s + 1) ^ 2 := by
    nlinarith [sq_nonneg (v - s)]
  have hexp : Real.exp (-(huangFilterTime c Delta L) ^ 2 / (2 * v)) ≤
      Real.exp (-s) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity : 0 < 2 * v)]
    dsimp only [huangFilterTime] at *
    nlinarith
  have hη := huangFilterEta_bounds hc L
  calc
    _ ≤ 2 * Real.exp (-s) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = huangFilterEta c L := by
      dsimp only [s]
      rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hη.1)]
      field_simp

/-- The excited-spectrum Gaussian multiplier is at most the precision.
Huang, Section 5.4, Lemma 18, with an energy estimate within half the gap. -/
theorem huangFilterVariance_suppression_le {c Delta : ℝ}
    (hc : 0 < c) (hDelta : 0 < Delta) (L : ℕ) :
    Real.exp (-(huangFilterVariance c Delta L : ℝ) * Delta ^ 2 / 8) ≤
      huangFilterEta c L := by
  rw [huangFilterVariance_coe hc]
  have hDelta2 : Delta ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hDelta)
  have hcancel : -(huangFilterScale c L / Delta ^ 2) * Delta ^ 2 / 8 =
      -Real.log (1 / huangFilterEta c L) - 1 := by
    dsimp only [huangFilterScale]
    field_simp
    ring
  rw [hcancel]
  calc
    _ ≤ Real.exp (-Real.log (1 / huangFilterEta c L)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = huangFilterEta c L := by
      rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr (huangFilterEta_bounds hc L).1)]
      simp

/-- The energy mesh is positive and at most half the gap; Huang, Section 5.4, Lemma 18. -/
theorem huangEnergyMesh_bounds {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) (L : ℕ) :
    0 < huangEnergyMesh c Delta L ∧ huangEnergyMesh c Delta L ≤ Delta / 2 := by
  have ha := huangFilterScale_ge_eight hc L
  constructor
  · exact div_pos hDelta (by linarith)
  · dsimp only [huangEnergyMesh]
    exact div_le_div_of_nonneg_left hDelta.le (by norm_num) (by linarith)

/-- Mesh accuracy gives both spectral half-gap accuracy and a variance-weighted energy
error at most one; Huang, Section 5.4, equation (19) and Lemma 18. -/
theorem huangEnergyMesh_accuracy {c Delta E E₀ : ℝ} (hc : 0 < c) (hDelta : 0 < Delta)
    (L : ℕ) (hE : |E - E₀| ≤ huangEnergyMesh c Delta L) :
    |E - E₀| ≤ Delta / 2 ∧
      (huangFilterVariance c Delta L : ℝ) * (E₀ - E) ^ 2 ≤ 1 := by
  refine ⟨hE.trans (huangEnergyMesh_bounds hc hDelta L).2, ?_⟩
  have ha := huangFilterScale_ge_eight hc L
  have hmesh := huangEnergyMesh_bounds hc hDelta L
  have hsq : (E₀ - E) ^ 2 ≤ (huangEnergyMesh c Delta L) ^ 2 := by
    rw [← neg_sub E E₀, neg_sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hE 2
  have hmul := mul_le_mul_of_nonneg_left hsq (huangFilterVariance_pos hc hDelta L).le
  refine hmul.trans ?_
  rw [huangFilterVariance_coe hc]
  dsimp only [huangEnergyMesh]
  have heq : huangFilterScale c L / Delta ^ 2 *
      (Delta / (huangFilterScale c L + 1)) ^ 2 =
      huangFilterScale c L / (huangFilterScale c L + 1) ^ 2 := by
    field_simp
  rw [heq]
  apply (div_le_one (by positivity : 0 < (huangFilterScale c L + 1) ^ 2)).mpr
  nlinarith

/-- The final overlap loss fits the prescribed inverse-length precision.
Huang, Section 5.4, supporting error budget for Lemmas 18--19. -/
theorem huangFilterEta_length_budget {c : ℝ} (hc : 0 < c) {L : ℕ} (hL : 1 ≤ L) :
    32 * huangFilterEta c L ≤ c / L := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden : 0 < 64 * (c + L + 1) := by positivity
  dsimp only [huangFilterEta]
  rw [le_div_iff₀ hLreal]
  rw [← mul_div_assoc, div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith

/-- A ground amplitude at least one half dominates twice the total filter error.
Huang, Section 5.4, supporting normalization estimate for Lemma 18. -/
theorem huangFilterEta_amplitude_budget {c c₀ : ℝ} (hc : 0 < c) (L : ℕ) (hc₀ : 1 / 2 ≤ c₀) :
    4 * huangFilterEta c L < c₀ / 2 := by
  have := (huangFilterEta_bounds hc L).2
  linarith

end TNLean.MPS.AreaLaw
