/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicScales
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-!
# Uniform separation of the three dyadic scales

The fixed exponents give an explicit threshold for any prescribed gap
between the fine-cell, layer-cell, and belt-pitch indices. Consequently,
any fixed multiplicative factor can be inserted between successive sides
at all sufficiently large scales. The threshold precedes the domain and cut.

Source: Section 11, `prop:two-families`, lines 200–207 of OpenAI,
*A two-dimensional area law from a global spectral gap* (September 24, 2026),
with the fixed values in `geometry:exponents`, lines 70–78.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Source revision:
  openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/
  sections/
  10-geometry.tex
Labels: prop:two-families; geometry:exponents.
Source lines: 70–78 and 200–207.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadicscale_index_gaps
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicScale_index_gaps
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadicscale_side_ratios
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicScale_side_ratios
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.exists_dyadicscale_side_ratios
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.exists_dyadicScale_side_ratios
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The fine and pitch indices are separated from the layer index by any
prescribed gap above an explicit uniform threshold.
Source: area-law Section 11, `prop:two-families`, lines 200–207,
and `geometry:exponents`, lines 70–78. -/
theorem dyadicScale_index_gaps (d k : ℕ) (hk : 10000000 * d ≤ k) :
    fineScaleIndex k + d ≤ k ∧ k + d ≤ pitchScaleIndex k := by
  have hd : d ≤ k := by omega
  have hk' : (10000000 : ℝ) * (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hf : fineScaleIndex k ≤ k - d := by
    unfold fineScaleIndex
    apply Nat.floor_le_of_le
    rw [Nat.cast_sub hd]
    norm_num [Exponents.zeta, Exponents.geometryDelta]
    linarith
  refine ⟨by omega, ?_⟩
  unfold pitchScaleIndex
  apply Nat.le_floor
  norm_num [Exponents.geometryDelta, Nat.cast_add]
  linarith [Nat.cast_nonneg (α := ℝ) d]

/-- Every prescribed dyadic factor separates the three cell sides above
the explicit index threshold.
Source: area-law Section 11, `prop:two-families`, lines 200–207. -/
theorem dyadicScale_side_ratios (d k : ℕ) (hk : 10000000 * d ≤ k) :
    (2 : ℕ) ^ d * 2 ^ fineScaleIndex k ≤ 2 ^ k ∧
      (2 : ℕ) ^ d * 2 ^ k ≤ 2 ^ pitchScaleIndex k := by
  obtain ⟨hf, hp⟩ := dyadicScale_index_gaps d k hk
  constructor
  · rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Every fixed multiplicative factor separates the fine-cell side, layer
side, and belt pitch at all sufficiently large scales. The threshold is
independent of the domain and cut.
Source: area-law Section 11, `prop:two-families`, lines 200–207. -/
theorem exists_dyadicScale_side_ratios (M : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      M * (2 : ℝ) ^ fineScaleIndex k ≤ (2 : ℝ) ^ k ∧
        M * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ pitchScaleIndex k := by
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 2)
  refine ⟨10000000 * d, ?_⟩
  intro k hk
  have h := dyadicScale_side_ratios d k hk
  have h' : (2 : ℝ) ^ d * (2 : ℝ) ^ fineScaleIndex k ≤ (2 : ℝ) ^ k ∧
      (2 : ℝ) ^ d * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ pitchScaleIndex k := by
    exact_mod_cast h
  constructor
  · exact (mul_le_mul_of_nonneg_right hd.le (pow_nonneg (by norm_num) _)).trans h'.1
  · exact (mul_le_mul_of_nonneg_right hd.le (pow_nonneg (by norm_num) _)).trans h'.2

end TNLean.PEPS.AreaLaw.Geometry
