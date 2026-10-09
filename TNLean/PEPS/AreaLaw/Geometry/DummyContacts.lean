/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DistanceLayers

/-!
# Contacts with the initial dummy neighborhood

A point in the closed initial neighborhood is at distance at most
\((C+1)2^k\) from an endpoint. The lower distance estimate for closed layers separates
that neighborhood from every layer beyond the initial one. Thus a shared
closure point with a layer above the lower index forces equality of the
indices.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 160–177 and 299–306.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Every point in a closed dyadic neighborhood has an endpoint at distance
at most \((C+1)2^k\). Source: area-law Section 11,
`geometry:layer-distance`, lines 160–177 and 179–191. -/
theorem dyadicNeighborhood_exists_dist_le (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (x : ℝ × ℝ)
    (hx : x ∈ closure (dyadicNeighborhood o k Z C)) :
    ∃ z ∈ Z, dist x (integerPoint z) ≤ ((C : ℝ) + 1) * (2 : ℝ) ^ k := by
  rw [dyadicNeighborhood, Finset.closure_biUnion] at hx
  obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp hx
  simp only [ambientDilation, Finset.mem_biUnion, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc] at hu
  obtain ⟨v, hv, huv⟩ := hu
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨z, hz,
    dyadicCell_dist_le o k u (dyadicCellIndex o k (integerPoint z)) C x (integerPoint z) hxu ?_ ?_⟩
  · exact subset_closure ((mem_dyadicCell_iff o k _ (integerPoint z)).mpr rfl)
  · simp only [abs_le, integerPoint]
    constructor <;> constructor <;> omega

/-- The closed initial neighborhood is separated from every later closed layer
by at least the excess dilation radius times its cell side. Source: area-law
Section 11, lines 160–177, `geometry:layer-distance`, lines 179–191, and 299–306. -/
theorem dyadicNeighborhood_dist_later_layer (o : ℝ × ℝ)
    (k₀ k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) (x y : ℝ × ℝ)
    (hk : k₀ + 1 ≤ k)
    (hx : x ∈ closure (dyadicNeighborhood o k₀ Z C))
    (hy : y ∈ closure (dyadicLayer o k Z C)) :
    ((C : ℝ) - 1) * (2 : ℝ) ^ k₀ ≤ dist x y := by
  obtain ⟨z, hz, hxz⟩ := dyadicNeighborhood_exists_dist_le o k₀ Z C x hx
  have hyz := dyadicLayer_dist_lower o k Z C y hy z hz
  have hpow : 2 * (2 : ℝ) ^ k₀ ≤ (2 : ℝ) ^ k := by
    calc
      2 * (2 : ℝ) ^ k₀ = (2 : ℝ) ^ (k₀ + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have ht : dist y (integerPoint z) ≤ dist x y + dist x (integerPoint z) := by
    simpa only [dist_comm y x] using dist_triangle y x (integerPoint z)
  nlinarith [mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg C : (0 : ℝ) ≤ C)]

/-- A closed layer at or above the lower index can share a point with the
closed dummy neighborhood only at that index. Source: area-law Section 11,
lines 160–177 and 299–306. -/
theorem dyadicNeighborhood_contact_layer_eq (o : ℝ × ℝ)
    (k₀ k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) (x : ℝ × ℝ)
    (hC : 2 ≤ C) (hk : k₀ ≤ k)
    (hx : x ∈ closure (dyadicNeighborhood o k₀ Z C))
    (hy : x ∈ closure (dyadicLayer o k Z C)) : k = k₀ := by
  by_contra hne
  have hsep := dyadicNeighborhood_dist_later_layer o k₀ k Z C x x (by omega) hx hy
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  exact (not_le_of_gt (mul_pos (by linarith : (0 : ℝ) < C - 1)
    (pow_pos zero_lt_two k₀))) (by simpa only [dist_self] using hsep)

end TNLean.PEPS.AreaLaw.Geometry
