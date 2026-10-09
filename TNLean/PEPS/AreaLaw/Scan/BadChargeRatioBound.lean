/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadHistoryGeometricTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The actual charge ratio at the rounded source capacity

The two-dimensional diamond count is at most thirteen times the squared
radius. The padded capacity is the ceiling of the source expression, so its
rounding only improves the bad-history estimate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 309–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type*}

/-- Cancellation of the physical row size in the actual charge ratio. -/
theorem badChargeRatio_le_radius_cube (S : CollarScan V I) (multiplicity : ℕ)
    {C1 : ℝ} (hC1 : 0 < C1) (hn : 0 < S.n) (hD : 0 < S.D)
    (hr : 1 ≤ S.r₀) (hM : C1 * S.n * S.D ≤ S.M) :
    S.badChargeRatio multiplicity ≤
      (117 * Real.exp 1 * multiplicity / (2 * C1)) * (S.r₀ : ℝ) ^ 3 / S.D := by
  have hnR : (0 : ℝ) < S.n := by exact_mod_cast hn
  have hDR : (0 : ℝ) < S.D := by exact_mod_cast hD
  have hrR : (1 : ℝ) ≤ S.r₀ := by exact_mod_cast hr
  have hMR : (0 : ℝ) < S.M := lt_of_lt_of_le (by positivity) hM
  have hball : (1 + 2 * (2 * S.r₀) * (2 * S.r₀ + 1) : ℝ) ≤
      13 * (S.r₀ : ℝ) ^ 2 := by nlinarith
  unfold badChargeRatio
  push_cast
  calc
    _ ≤ Real.exp 1 * (9 * (S.n : ℝ) * S.r₀) *
        ((13 * (S.r₀ : ℝ) ^ 2 * multiplicity) / (2 * (C1 * S.n * S.D))) := by
      gcongr
    _ = _ := by field_simp; ring

/-- Floors do not increase either source length beyond the ambient scale. -/
theorem source_lengths_le {n : ℕ} {ell mu : ℝ} (hn : 1 ≤ n)
    (hell : 0 ≤ ell) (hmu : mu ≤ 1) :
    ⌊(n : ℝ) ^ (1 - ell)⌋₊ ≤ n ∧ ⌊(n : ℝ) ^ mu⌋₊ ≤ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact_mod_cast (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
      ((Real.rpow_le_rpow_of_exponent_le hnR (by linarith : 1 - ell ≤ 1)).trans_eq
        (Real.rpow_one _))
  · exact_mod_cast (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
      ((Real.rpow_le_rpow_of_exponent_le hnR hmu).trans_eq (Real.rpow_one _))

end TNLean.PEPS.AreaLaw.Scan.CollarScan
