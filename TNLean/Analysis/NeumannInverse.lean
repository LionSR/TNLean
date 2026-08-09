/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Ring.Units

/-!
# A quantitative Neumann inverse bound

This file records the denominator estimate used for inverse Gram operators.
-/

namespace NormedRing

variable {R : Type*} [NormedRing R] [NormOneClass R] [HasSummableGeomSeries R]

/-- Quantitative Neumann bound.  If \(\lVert t\rVert\le a<1\), then
\(\lVert(1-t)^{-1}\rVert\le(1-a)^{-1}\). -/
theorem norm_inverse_one_sub_le (t : R) {a : ℝ} (ht : ‖t‖ ≤ a) (ha : a < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ (1 - a)⁻¹ := by
  have ht_one : ‖t‖ < 1 := ht.trans_lt ha
  rw [inverse_one_sub t ht_one]
  change ‖∑' n : ℕ, t ^ n‖ ≤ (1 - a)⁻¹
  calc
    ‖∑' n : ℕ, t ^ n‖ ≤ (1 - ‖t‖)⁻¹ := by
      simpa using tsum_geometric_le_of_norm_lt_one t ht_one
    _ ≤ (1 - a)⁻¹ := by
      exact (inv_le_inv₀ (sub_pos.mpr ht_one) (sub_pos.mpr ha)).2 (by linarith)

end NormedRing
