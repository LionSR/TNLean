/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DistanceLayers
import TNLean.PEPS.AreaLaw.Geometry.ScaleSeparation

/-!
# Only neighboring layers occur at a fine-cell distance

Beyond one fixed index threshold, nonadjacent closed distance layers are
separated by at least sixteen fine-cell sides. Consequently a neighborhood
of radius ten fine-cell sides sees only the same or an adjacent layer.
The threshold is chosen before the endpoint set, origin and points.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–356.
The proof uses `geometry:nonadjacent` and the uniform dyadic scale ratios.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Nonadjacent actual layers have a uniform fine-scale distance bound.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–356. -/
theorem dyadicLayer_dist_nonadjacent_fineScale (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (x y : ℝ × ℝ)
    (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hkh : k + 2 ≤ h ∨ h + 2 ≤ k)
    (hx : x ∈ closure (dyadicLayer o k Z C))
    (hy : y ∈ closure (dyadicLayer o h Z C)) :
    16 * (2 : ℝ) ^ fineScaleIndex k ≤ dist x y := by
  have hscale : (2 : ℝ) ^ 5 * (2 : ℝ) ^ fineScaleIndex k ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (dyadicScale_side_ratios 5 k (by omega)).1
  norm_num at hscale
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hbound (j : ℕ) (hkj : k ≤ j) :
      16 * (2 : ℝ) ^ fineScaleIndex k ≤ ((C : ℝ) - 1) / 2 * (2 : ℝ) ^ j := by
    calc
      _ ≤ (1 / 2 : ℝ) * 2 ^ k := by linarith
      _ ≤ (1 / 2 : ℝ) * 2 ^ j :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hkj) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rcases hkh with hkh | hhk
  · exact (hbound h (by omega)).trans
      (dyadicLayer_dist_nonadjacent o k h Z C x y hkh hx hy)
  · have hsep := dyadicLayer_dist_nonadjacent o h k Z C y x hhk hy hx
    rw [dist_comm] at hsep
    exact (hbound k le_rfl).trans hsep

/-- A point at distance less than ten fine-cell sides can belong only to
the same or an adjacent actual layer.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–356. -/
theorem dyadicLayer_nearby_indices (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (x y : ℝ × ℝ)
    (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hx : x ∈ closure (dyadicLayer o k Z C))
    (hy : y ∈ closure (dyadicLayer o h Z C))
    (hnear : dist x y < 10 * (2 : ℝ) ^ fineScaleIndex k) :
    h ≤ k + 1 ∧ k ≤ h + 1 := by
  have hnot : ¬ (k + 2 ≤ h ∨ h + 2 ≤ k) := by
    intro hkh
    have hsep := dyadicLayer_dist_nonadjacent_fineScale o k h Z C x y hC hk hkh hx hy
    have ht := pow_pos (by norm_num : (0 : ℝ) < 2) (fineScaleIndex k)
    linarith
  omega

end TNLean.PEPS.AreaLaw.Geometry
