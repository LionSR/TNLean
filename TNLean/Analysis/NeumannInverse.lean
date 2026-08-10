/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Ring.Units

/-!
# A quantitative Neumann inverse bound

This file records quantitative Neumann bounds, both around the identity and around an
arbitrary invertible base point.  The latter estimates control the inverse and its displacement
under a relatively small perturbation.
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

/-- If `K₀` is a unit and its relative perturbation toward `K` has norm at most `a < 1`,
then `K` is a unit and its inverse is bounded by
`(1 - a)⁻¹ * ‖Ring.inverse K₀‖`. -/
theorem isUnit_and_norm_inverse_le_of_norm_inverse_mul_sub_le (K₀ K : R) {a : ℝ}
    (hK₀ : IsUnit K₀) (h : ‖Ring.inverse K₀ * (K - K₀)‖ ≤ a) (ha : a < 1) :
    IsUnit K ∧ ‖Ring.inverse K‖ ≤ (1 - a)⁻¹ * ‖Ring.inverse K₀‖ := by
  let E := Ring.inverse K₀ * (K - K₀)
  have hE : ‖E‖ ≤ a := h
  have hE_lt_one : ‖E‖ < 1 := hE.trans_lt ha
  have hbase : IsUnit (1 - -E) :=
    isUnit_one_sub_of_norm_lt_one (by simpa using hE_lt_one)
  have hfactor : K = K₀ * (1 - -E) := by
    dsimp [E]
    rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc,
      Ring.mul_inverse_cancel K₀ hK₀, one_mul]
    abel
  have hinverse : Ring.inverse K = Ring.inverse (1 - -E) * Ring.inverse K₀ := by
    rw [hfactor, Ring.inverse_mul (Or.inl hK₀)]
  constructor
  · rw [hfactor]
    exact hK₀.mul hbase
  · rw [hinverse]
    calc
      ‖Ring.inverse (1 - -E) * Ring.inverse K₀‖ ≤
          ‖Ring.inverse (1 - -E)‖ * ‖Ring.inverse K₀‖ := norm_mul_le _ _
      _ ≤ (1 - a)⁻¹ * ‖Ring.inverse K₀‖ := by
        gcongr
        exact norm_inverse_one_sub_le (-E) (by simpa using hE) ha

/-- A product-form version of
`isUnit_and_norm_inverse_le_of_norm_inverse_mul_sub_le`.  This is convenient when the
relative perturbation is estimated by submultiplicativity of the norm. -/
theorem isUnit_and_norm_inverse_le_of_norm_mul_norm_sub_le (K₀ K : R) {a : ℝ}
    (hK₀ : IsUnit K₀) (h : ‖Ring.inverse K₀‖ * ‖K - K₀‖ ≤ a) (ha : a < 1) :
    IsUnit K ∧ ‖Ring.inverse K‖ ≤ (1 - a)⁻¹ * ‖Ring.inverse K₀‖ := by
  apply isUnit_and_norm_inverse_le_of_norm_inverse_mul_sub_le K₀ K hK₀ _ ha
  exact (norm_mul_le _ _).trans h

/-- Under a relative perturbation of size at most `a < 1`, the displacement of the inverse
from the base inverse is at most `(1 - a)⁻¹ * a * ‖Ring.inverse K₀‖`. -/
theorem norm_inverse_sub_inverse_le_of_norm_inverse_mul_sub_le (K₀ K : R) {a : ℝ}
    (hK₀ : IsUnit K₀) (h : ‖Ring.inverse K₀ * (K - K₀)‖ ≤ a) (ha : a < 1) :
    ‖Ring.inverse K - Ring.inverse K₀‖ ≤
      (1 - a)⁻¹ * a * ‖Ring.inverse K₀‖ := by
  let E := Ring.inverse K₀ * (K - K₀)
  have hE : ‖E‖ ≤ a := h
  have hE_lt_one : ‖E‖ < 1 := hE.trans_lt ha
  have hbase : IsUnit (1 - -E) :=
    isUnit_one_sub_of_norm_lt_one (by simpa using hE_lt_one)
  have hfactor : K = K₀ * (1 - -E) := by
    dsimp [E]
    rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc,
      Ring.mul_inverse_cancel K₀ hK₀, one_mul]
    abel
  have hinverse : Ring.inverse K = Ring.inverse (1 - -E) * Ring.inverse K₀ := by
    rw [hfactor, Ring.inverse_mul (Or.inl hK₀)]
  have hresolvent :
      Ring.inverse K - Ring.inverse K₀ =
        -(Ring.inverse (1 - -E) * E) * Ring.inverse K₀ := by
    have hcancel :
        Ring.inverse (1 - -E) + Ring.inverse (1 - -E) * E = 1 := by
      calc
        Ring.inverse (1 - -E) + Ring.inverse (1 - -E) * E =
            Ring.inverse (1 - -E) * (1 - -E) := by
          simp only [sub_neg_eq_add, mul_add, mul_one]
        _ = 1 := Ring.inverse_mul_cancel (1 - -E) hbase
    have hdifference :
        Ring.inverse (1 - -E) - 1 = -(Ring.inverse (1 - -E) * E) := by
      calc
        Ring.inverse (1 - -E) - 1 =
            Ring.inverse (1 - -E) -
              (Ring.inverse (1 - -E) + Ring.inverse (1 - -E) * E) :=
          congrArg (Ring.inverse (1 - -E) - ·) hcancel.symm
        _ = -(Ring.inverse (1 - -E) * E) := by noncomm_ring
    rw [hinverse]
    calc
      Ring.inverse (1 - -E) * Ring.inverse K₀ - Ring.inverse K₀ =
          (Ring.inverse (1 - -E) - 1) * Ring.inverse K₀ := by noncomm_ring
      _ = -(Ring.inverse (1 - -E) * E) * Ring.inverse K₀ := by rw [hdifference]
  rw [hresolvent]
  have hneumann : ‖Ring.inverse (1 - -E)‖ ≤ (1 - a)⁻¹ :=
    norm_inverse_one_sub_le (-E) (by simpa using hE) ha
  have ha_nonneg : 0 ≤ a := (norm_nonneg E).trans hE
  have hdenom_nonneg : 0 ≤ (1 - a)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr ha.le)
  calc
    ‖-(Ring.inverse (1 - -E) * E) * Ring.inverse K₀‖ ≤
        ‖-(Ring.inverse (1 - -E) * E)‖ * ‖Ring.inverse K₀‖ := norm_mul_le _ _
    _ ≤ (‖Ring.inverse (1 - -E)‖ * ‖E‖) * ‖Ring.inverse K₀‖ := by
      gcongr
      simpa only [norm_neg] using norm_mul_le (Ring.inverse (1 - -E)) E
    _ ≤ ((1 - a)⁻¹ * a) * ‖Ring.inverse K₀‖ := by
      gcongr
    _ = (1 - a)⁻¹ * a * ‖Ring.inverse K₀‖ := rfl

/-- A product-form inverse-displacement estimate, obtained from
`‖Ring.inverse K₀ * (K - K₀)‖ ≤ ‖Ring.inverse K₀‖ * ‖K - K₀‖`. -/
theorem norm_inverse_sub_inverse_le_of_norm_mul_norm_sub_le (K₀ K : R) {a : ℝ}
    (hK₀ : IsUnit K₀) (h : ‖Ring.inverse K₀‖ * ‖K - K₀‖ ≤ a) (ha : a < 1) :
    ‖Ring.inverse K - Ring.inverse K₀‖ ≤
      (1 - a)⁻¹ * a * ‖Ring.inverse K₀‖ := by
  apply norm_inverse_sub_inverse_le_of_norm_inverse_mul_sub_le K₀ K hK₀ _ ha
  exact (norm_mul_le _ _).trans h

end NormedRing
