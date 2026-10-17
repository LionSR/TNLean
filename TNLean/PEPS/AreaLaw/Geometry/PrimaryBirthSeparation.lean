/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.PrimaryRegions
import TNLean.PEPS.AreaLaw.Geometry.DyadicScales

/-!
# Separation of primary births in layers of the same parity

Distinct primary births in one layer are separated by the belt width.
Layers of the same parity are either equal or differ by at least two;
in the latter case the closed-layer separation gives a lower bound at
least half the layer scale of either primary. The resulting minimum
bound is independent of how the primary identifiers are ordered.

This is an auxiliary geometric consequence of OpenAI,
*A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 11, `10-geometry.tex`, `geometry:nonadjacent`, lines 192–197,
primary pieces and labels, lines 239–249, and the primary comparison in
lines 784–789. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Distinct primary closed births in layers of the same parity are separated
by the smaller of the reference layer's belt width and half its layer scale.
The shifts may vary with the layer; within a layer the same shifts are used.
This includes every natural layer index and requires no nonemptiness or
finiteness assumption on an identifier family.

Auxiliary to area-law Section 11, `geometry:nonadjacent`, `10-geometry.tex`,
lines 192–197; same-layer separation and opposite labels in adjacent layers,
lines 239–249; and the primary case of ordered clearance, lines 784–789. -/
theorem primaryBirthRegion_dist_separation_of_same_parity
    (o : ℝ × ℝ) (k h : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : ℕ → ℤ) (i j : ℤ × ℤ) (hC : 2 ≤ C)
    (hpar : k % 2 = h % 2) (hij : (k, i) ≠ (h, j))
    (x y : ℝ × ℝ)
    (hx : x ∈ primaryBirthRegion o k (fineScaleIndex k) (pitchScaleIndex k)
      Z C (a k) (b k) i)
    (hy : y ∈ primaryBirthRegion o h (fineScaleIndex h) (pitchScaleIndex h)
      Z C (a h) (b h) j) :
    min ((2 : ℝ) ^ fineScaleIndex k) ((2 : ℝ) ^ k / 2) ≤ dist x y := by
  classical
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  rcases lt_trichotomy k h with hkh | rfl | hhk
  · have hsep := dyadicLayer_dist_nonadjacent o k h Z C x y
      (by omega) (closure_mono Set.inter_subset_left hx)
      (closure_mono Set.inter_subset_left hy)
    have hpow : (2 : ℝ) ^ k ≤ 2 ^ h :=
      pow_le_pow_right₀ (by norm_num) hkh.le
    exact (min_le_right _ _).trans (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC')
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) h)])
  · exact (min_le_left _ _).trans
      (primaryBirthRegion_dist_separation o k (fineScaleIndex k) (pitchScaleIndex k)
        Z C (a k) (b k) i j (fun he ↦ hij (Prod.ext rfl he)) x y hx hy)
  · have hsep : ((C : ℝ) - 1) / 2 * (2 : ℝ) ^ k ≤ dist x y := by
      simpa only [dist_comm y x] using
        (dyadicLayer_dist_nonadjacent o h k Z C y x
          (by omega) (closure_mono Set.inter_subset_left hy)
          (closure_mono Set.inter_subset_left hx))
    exact (min_le_right _ _).trans (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC')
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)])

end TNLean.PEPS.AreaLaw.Geometry
