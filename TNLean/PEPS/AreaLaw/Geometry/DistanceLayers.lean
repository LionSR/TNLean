/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicClosure
import TNLean.PEPS.AreaLaw.Geometry.Templates
import Mathlib.Topology.MetricSpace.HausdorffDistance
/-!
# Distance bounds for closed dyadic layers

Closed cells outside the endpoint neighborhood are at least the dilation
radius times the cell side from every endpoint. A point in a closed layer
also lies in the closure of the next neighborhood, giving an endpoint at
distance at most twice the dilation width times that side. The metric on
`ℝ × ℝ` is the sup metric.

The triangle inequality combines these bounds into the uniform separation
of layers whose indices differ by at least two. The origin is arbitrary,
and scales and radii are nonnegative integers. Pointwise statements include
empty layers; whenever a layer point exists, the upper-distance witness
also proves that the endpoint set is nonempty.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `geometry:layer-distance` and
  `geometry:nonadjacent`, source lines 179–204.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/sections/10-geometry.tex
Labels: geometry:layer-distance, geometry:nonadjacent.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiccell_dist_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicCell_dist_le
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiccell_dist_lower
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicCell_dist_lower
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiclayer_dist_lower
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_dist_lower
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiclayer_exists_dist_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_exists_dist_le
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiclayer_infdist_bounds
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_infDist_bounds
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiclayer_dist_separation
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_dist_separation
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiclayer_dist_nonadjacent
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_dist_nonadjacent
-/

namespace TNLean.PEPS.AreaLaw.Geometry
private theorem interval_dist_le {o r u v C x y : ℝ} (hr : 0 ≤ r)
    (huv : |u - v| ≤ C)
    (hx : o + r * u ≤ x ∧ x ≤ o + r * (u + 1))
    (hy : o + r * v ≤ y ∧ y ≤ o + r * (v + 1)) :
    |x - y| ≤ (C + 1) * r := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp huv
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlo hr,
    mul_le_mul_of_nonneg_left hhi hr]
/-- Nearby closed dyadic cells have sup distance at most the index radius plus one cell width.
Source: area-law Section 11, `geometry:layer-distance`, lines 184–191. -/
theorem dyadicCell_dist_le (o : ℝ × ℝ) (k : ℕ) (u v : ℤ × ℤ) (C : ℕ)
    (x y : ℝ × ℝ) (hx : x ∈ closure (dyadicCell o k u))
    (hy : y ∈ closure (dyadicCell o k v))
    (huv : |u.1 - v.1| ≤ (C : ℤ) ∧ |u.2 - v.2| ≤ (C : ℤ)) :
    dist x y ≤ ((C : ℝ) + 1) * (2 : ℝ) ^ k := by
  simp only [closure_dyadicCell, Set.mem_prod, Set.mem_Icc] at hx hy
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
  exact ⟨interval_dist_le (pow_nonneg (by norm_num) k)
    (by exact_mod_cast huv.1) hx.1 hy.1,
    interval_dist_le (pow_nonneg (by norm_num) k)
      (by exact_mod_cast huv.2) hx.2 hy.2⟩
private theorem exists_dist_le_of_mem_closure_dyadicNeighborhood
    (o : ℝ × ℝ) (k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) (x : ℝ × ℝ)
    (hx : x ∈ closure (dyadicNeighborhood o k Z C)) :
    ∃ z ∈ Z, dist x (integerPoint z) ≤ ((C : ℝ) + 1) * (2 : ℝ) ^ k := by
  rw [dyadicNeighborhood, Finset.closure_biUnion] at hx
  obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp hx
  simp only [ambientDilation, Finset.mem_biUnion, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc] at hu
  obtain ⟨v, hv, huv⟩ := hu
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨z, hz, dyadicCell_dist_le o k u (dyadicCellIndex o k (integerPoint z)) C x (integerPoint z) hxu ?_ ?_⟩
  · exact subset_closure ((mem_dyadicCell_iff o k _ (integerPoint z)).mpr rfl)
  · simp only [abs_le, integerPoint]
    constructor <;> constructor <;> omega
/-- Every point in a closed dyadic layer has an endpoint at distance at most
twice the dilation width times its cell side.
Source: area-law Section 11, `geometry:layer-distance`, lines 184–191. -/
theorem dyadicLayer_exists_dist_le (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (x : ℝ × ℝ)
    (hx : x ∈ closure (dyadicLayer o k Z C)) :
    ∃ z ∈ Z, dist x (integerPoint z) ≤ 2 * ((C : ℝ) + 1) * (2 : ℝ) ^ k := by
  have hx' : x ∈ closure (dyadicNeighborhood o (k + 1) Z C) :=
    closure_mono Set.sdiff_subset hx
  obtain ⟨z, hz, hd⟩ :=
    exists_dist_le_of_mem_closure_dyadicNeighborhood o (k + 1) Z C x hx'
  refine ⟨z, hz, ?_⟩
  simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hd

private theorem interval_dist_lower (o r : ℝ) (hr : 0 < r) (u v : ℤ) (C : ℕ)
    (x y : ℝ) (hx : o + r * u ≤ x ∧ x ≤ o + r * (u + 1))
    (hy : o + r * v ≤ y ∧ y ≤ o + r * (v + 1))
    (hfar : (C : ℤ) < |u - v|) : (C : ℝ) * r ≤ |x - y| := by
  by_cases huv : u ≤ v
  · have hgap : (C : ℤ) + 1 ≤ v - u := by
      rw [abs_of_nonpos (sub_nonpos.mpr huv)] at hfar
      omega
    have hgap' : (C : ℝ) + 1 ≤ (v : ℝ) - (u : ℝ) := by exact_mod_cast hgap
    calc
      (C : ℝ) * r ≤ y - x := by
        nlinarith [mul_le_mul_of_nonneg_left hgap' hr.le]
      _ ≤ |x - y| := by simpa [abs_sub_comm] using le_abs_self (y - x)
  · have hgap : (C : ℤ) + 1 ≤ u - v := by
      rw [abs_of_nonneg (by omega : 0 ≤ u - v)] at hfar
      omega
    have hgap' : (C : ℝ) + 1 ≤ (u : ℝ) - (v : ℝ) := by exact_mod_cast hgap
    calc
      (C : ℝ) * r ≤ x - y := by
        nlinarith [mul_le_mul_of_nonneg_left hgap' hr.le]
      _ ≤ |x - y| := le_abs_self _

/-- Closed dyadic cells separated by more than the dilation radius in one
integer coordinate are separated by at least the radius times their side.
Source: area-law Section 11, `geometry:layer-distance`, lines 179–189. -/
theorem dyadicCell_dist_lower (o : ℝ × ℝ) (k : ℕ) (u v : ℤ × ℤ) (C : ℕ)
    (x y : ℝ × ℝ) (hx : x ∈ closure (dyadicCell o k u))
    (hy : y ∈ closure (dyadicCell o k v))
    (hfar : (C : ℤ) < |u.1 - v.1| ∨ (C : ℤ) < |u.2 - v.2|) :
    (C : ℝ) * (2 : ℝ) ^ k ≤ dist x y := by
  rw [closure_dyadicCell] at hx hy
  simp only [Set.mem_prod, Set.mem_Icc] at hx hy
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  obtain hfar | hfar := hfar
  · exact (interval_dist_lower o.1 ((2 : ℝ) ^ k) (pow_pos zero_lt_two k)
      u.1 v.1 C x.1 y.1 hx.1 hy.1 hfar).trans (le_max_left _ _)
  · exact (interval_dist_lower o.2 ((2 : ℝ) ^ k) (pow_pos zero_lt_two k)
      u.2 v.2 C x.2 y.2 hx.2 hy.2 hfar).trans (le_max_right _ _)

/-- Every point in the closure of a dyadic layer is at least the dilation
radius times the cell side from every endpoint.
Source: area-law Section 11, `geometry:layer-distance`, lines 179–189. -/
theorem dyadicLayer_dist_lower (o : ℝ × ℝ) (k : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (x : ℝ × ℝ) (hx : x ∈ closure (dyadicLayer o k Z C))
    (z : ℤ × ℤ) (hz : z ∈ Z) :
    (C : ℝ) * (2 : ℝ) ^ k ≤ dist x (integerPoint z) := by
  rw [closure_dyadicLayer_eq_iUnion] at hx
  obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp hx
  have hu' := (Finset.mem_sdiff.mp hu).2
  let v := dyadicCellIndex o k (integerPoint z)
  have hv : v ∈ occupiedCellIndices o k Z := Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hzv : integerPoint z ∈ closure (dyadicCell o k v) :=
    subset_closure ((mem_dyadicCell_iff o k v (integerPoint z)).mpr rfl)
  have hfar : (C : ℤ) < |u.1 - v.1| ∨ (C : ℤ) < |u.2 - v.2| := by
    by_contra h
    have hb : |u.1 - v.1| ≤ (C : ℤ) ∧ |u.2 - v.2| ≤ (C : ℤ) := by omega
    apply hu'
    simp only [ambientDilation, Finset.mem_biUnion, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_Icc]
    refine ⟨v, hv, ?_⟩
    simp only [abs_le] at hb
    constructor <;> constructor <;> omega
  exact dyadicCell_dist_lower o k u v C x (integerPoint z) hxu hzv hfar

/-- The distance of a closed dyadic layer to the endpoints lies between the
radius times the cell side and twice the dilation width times that side.
Source: area-law Section 11, `geometry:layer-distance`, lines 184–191. -/
theorem dyadicLayer_infDist_bounds (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (x : ℝ × ℝ)
    (hx : x ∈ closure (dyadicLayer o k Z C)) :
    (C : ℝ) * (2 : ℝ) ^ k ≤ Metric.infDist x (integerPoint '' (Z : Set (ℤ × ℤ))) ∧
      Metric.infDist x (integerPoint '' (Z : Set (ℤ × ℤ))) ≤
        2 * ((C : ℝ) + 1) * (2 : ℝ) ^ k := by
  obtain ⟨z, hz, hd⟩ := dyadicLayer_exists_dist_le o k Z C x hx
  have hmem : integerPoint z ∈ integerPoint '' (Z : Set (ℤ × ℤ)) :=
    Set.mem_image_of_mem integerPoint hz
  refine ⟨(Metric.le_infDist ⟨integerPoint z, hmem⟩).mpr ?_,
    (Metric.infDist_le_dist_of_mem hmem).trans hd⟩
  rintro y ⟨w, hw, rfl⟩
  exact dyadicLayer_dist_lower o k Z C x hx w hw
/-- Two closed layers are separated by the difference between the outer
lower endpoint distance and the inner upper endpoint distance.
Source: area-law Section 11, `geometry:nonadjacent`, lines 193–204. -/
theorem dyadicLayer_dist_separation (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (x y : ℝ × ℝ)
    (hx : x ∈ closure (dyadicLayer o k Z C))
    (hy : y ∈ closure (dyadicLayer o h Z C)) :
    (C : ℝ) * (2 : ℝ) ^ h - 2 * ((C : ℝ) + 1) * (2 : ℝ) ^ k ≤ dist x y := by
  obtain ⟨z, hz, hxz⟩ := dyadicLayer_exists_dist_le o k Z C x hx
  have hyz := dyadicLayer_dist_lower o h Z C y hy z hz
  have ht := dist_triangle y x (integerPoint z)
  rw [dist_comm y x] at ht
  linarith

/-- Layers whose indices differ by at least two have the source's uniform
sup-distance lower bound.
Source: area-law Section 11, `geometry:nonadjacent`, lines 193–204. -/
theorem dyadicLayer_dist_nonadjacent (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (x y : ℝ × ℝ)
    (hkh : k + 2 ≤ h) (hx : x ∈ closure (dyadicLayer o k Z C))
    (hy : y ∈ closure (dyadicLayer o h Z C)) :
    ((C : ℝ) - 1) / 2 * (2 : ℝ) ^ h ≤ dist x y := by
  have hpow : 4 * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ h := by
    calc
      4 * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 2) := by ring
      _ ≤ (2 : ℝ) ^ h := pow_le_pow_right₀ (by norm_num) hkh
  have hsep := dyadicLayer_dist_separation o k h Z C x y hx hy
  nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (C : ℝ) + 1)]
end TNLean.PEPS.AreaLaw.Geometry
