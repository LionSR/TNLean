/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Exponents
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic.Linarith

/-!
# Arithmetic of the fine-cell and belt scales

The fine-cell side length divides the layer-cell side length, which in turn
divides the belt pitch. Rounding the two exponents costs less than two in
their sum. These are the arithmetic ingredients in the sparse-belt estimate.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `geometry:belt-count`, lines 200–237.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/
  sections/
  10-geometry.tex
Labels: geometry:belt-count.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.finescaleindex
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.fineScaleIndex
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.pitchscaleindex
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.pitchScaleIndex
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.finescaleindex_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.fineScaleIndex_le
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.le_pitchscaleindex
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.le_pitchScaleIndex
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.finescale_dvd_layerscale
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.fineScale_dvd_layerScale
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.layerscale_dvd_pitchscale
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.layerScale_dvd_pitchScale
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.layerscale_exponent_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.layerScale_exponent_le
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Exponent of the fine-cell side length at scale `k`.
Source: Section 11, `10-geometry.tex`, lines 200–205. -/
def fineScaleIndex (k : ℕ) : ℕ := Nat.floor ((Exponents.zeta : ℝ) * (k : ℝ))

/-- Exponent of the belt pitch at scale `k`.
Source: Section 11, `10-geometry.tex`, lines 200–205. -/
def pitchScaleIndex (k : ℕ) : ℕ :=
  Nat.floor ((1 + (Exponents.geometryDelta : ℝ)) * (k : ℝ))

/-- The fine-cell exponent does not exceed the layer-cell exponent.
Source: Section 11, `10-geometry.tex`, lines 205–207. -/
theorem fineScaleIndex_le (k : ℕ) : fineScaleIndex k ≤ k := by
  apply Nat.floor_le_of_le
  have hz : (Exponents.zeta : ℝ) ≤ 1 := by
    exact_mod_cast Exponents.geometry_gaps.2.1.le
  simpa using mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg k)

/-- The layer-cell exponent does not exceed the belt-pitch exponent.
Source: Section 11, `10-geometry.tex`, lines 205–207. -/
theorem le_pitchScaleIndex (k : ℕ) : k ≤ pitchScaleIndex k := by
  apply Nat.le_floor
  have hδ : 0 ≤ (Exponents.geometryDelta : ℝ) := by
    norm_num [Exponents.geometryDelta]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- Every fine-cell side length divides the corresponding layer-cell side length.
Source: Section 11, `10-geometry.tex`, lines 205–207. -/
theorem fineScale_dvd_layerScale (k : ℕ) : 2 ^ fineScaleIndex k ∣ (2 : ℕ) ^ k :=
  pow_dvd_pow 2 (fineScaleIndex_le k)

/-- Every layer-cell side length divides the corresponding belt pitch.
Source: Section 11, `10-geometry.tex`, lines 205–207. -/
theorem layerScale_dvd_pitchScale (k : ℕ) : (2 : ℕ) ^ k ∣ 2 ^ pitchScaleIndex k :=
  pow_dvd_pow 2 (le_pitchScaleIndex k)

/-- The two rounded scale exponents yield the geometric decay exponent, up to
an additive constant of two.
Source: Section 11, `10-geometry.tex`, lines 220–228 (`geometry:belt-count`). -/
theorem layerScale_exponent_le (k : ℕ) :
    2 * (k : ℝ) - (pitchScaleIndex k : ℝ) - (fineScaleIndex k : ℝ) ≤
      2 - (Exponents.geometryDelta : ℝ) * (k : ℝ) / 2 := by
  have hf := Nat.lt_floor_add_one ((Exponents.zeta : ℝ) * (k : ℝ))
  have hp := Nat.lt_floor_add_one ((1 + (Exponents.geometryDelta : ℝ)) * (k : ℝ))
  have hz : (Exponents.zeta : ℝ) = 1 - (Exponents.geometryDelta : ℝ) / 2 := by
    simp [Exponents.zeta]
  change (Exponents.zeta : ℝ) * (k : ℝ) < (fineScaleIndex k : ℝ) + 1 at hf
  change (1 + (Exponents.geometryDelta : ℝ)) * (k : ℝ) <
    (pitchScaleIndex k : ℝ) + 1 at hp
  rw [hz] at hf
  nlinarith

end TNLean.PEPS.AreaLaw.Geometry
