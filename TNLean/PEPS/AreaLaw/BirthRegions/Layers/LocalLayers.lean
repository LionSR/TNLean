/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Dyadic.DyadicClosure
import QICLean.ManyBody.Sites.Template.Defs
import Mathlib.Topology.MetricSpace.HausdorffDistance
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.ScaleSeparation
import QICLean.ManyBody.Sites.Dyadic.DyadicLayers
import QICLean.ManyBody.Sites.Dyadic.DyadicRefinement
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.DyadicScales
import QICLean.ManyBody.Sites.Dyadic.DistanceLayers
import QICLean.ManyBody.Sites.Dyadic.LayerPartition

/-!
# Neighbouring dyadic layers and fine cells

Two facts about the translated dyadic layers of Section 11 at the fine scale of the birth
regions: beyond one index threshold only the same or an adjacent layer occurs within a
fine-cell distance, and a point outside the dyadic neighbourhood lies in exactly one fine cell
of the later layers. The distances and partitions of the layers themselves are
`QICLean.ManyBody.Sites.Dyadic.DistanceLayers` and `QICLean.ManyBody.Sites.Dyadic.LayerPartition`.

* `TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_dist_nonadjacent_fineScale`,
  `TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_nearby_indices`: only neighbouring layers occur at a
  fine-cell distance.
* `TNLean.PEPS.AreaLaw.Geometry.exists_unique_fineCell_of_not_mem_dyadicNeighborhood`,
  `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_union_iUnion_fineCells_eq_univ`: the fine
  cells partition the complement of the neighbourhood.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–356.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (dyadicLayer dyadicLayer_dist_nonadjacent)

section LocalLayers

/-!
## Only neighboring layers occur at a fine-cell distance

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

end LocalLayers

open ManyBody (dyadicCell dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices
  dyadicLayer_eq_iUnion_fine dyadicNeighborhood exists_unique_layer_of_not_mem_dyadicNeighborhood
  fineLayerIndices mem_dyadicCell_iff)

namespace TNLean.PEPS.AreaLaw.Geometry

section FineCellPartition

/-!
## Unique actual fine-cell assignment outside the dummy region

For a nonempty endpoint set and dilation width at least two, the unique
half-open layer assignment and the exact finer-cell union give
a unique actual fine cell for every point outside the initial neighborhood.
Consequently that neighborhood and all later actual fine cells cover the plane.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 154–181 and 200–207.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-- Outside the initial neighborhood there is a unique actually indexed fine cell
at or above the lower index. Source: area-law Section 11, `prop:two-families`,
lines 154–181 and 200–207. -/
theorem exists_unique_fineCell_of_not_mem_dyadicNeighborhood (o : ℝ × ℝ)
    (Z : Finset (ℤ × ℤ)) (C k₀ : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C)
    (x : ℝ × ℝ) (hx : x ∉ dyadicNeighborhood o k₀ Z C) :
    ∃! p : ℕ × (ℤ × ℤ), k₀ ≤ p.1 ∧
      p.2 ∈ fineLayerIndices o p.1 (fineScaleIndex p.1) Z C ∧
      x ∈ dyadicCell o (fineScaleIndex p.1) p.2 := by
  obtain ⟨k, ⟨hk, hxk⟩, huniq⟩ :=
    exists_unique_layer_of_not_mem_dyadicNeighborhood o Z C k₀ hZ hC x hx
  rw [dyadicLayer_eq_iUnion_fine o k (fineScaleIndex k) Z C (fineScaleIndex_le k)] at hxk
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hxk
  refine ⟨(k, z), ⟨hk, hz, hxz⟩, ?_⟩
  rintro ⟨h, w⟩ ⟨hh, hw, hxw⟩
  have hhk : h = k := huniq h ⟨hh,
    dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h
      (fineScaleIndex h) Z C w (fineScaleIndex_le h) hw hxw⟩
  subst h
  exact Prod.ext rfl
    (((mem_dyadicCell_iff o (fineScaleIndex k) w x).mp hxw).symm.trans
      ((mem_dyadicCell_iff o (fineScaleIndex k) z x).mp hxz))

/-- The initial neighborhood and all actual fine cells at or above its lower
index cover the plane exactly. Source: area-law Section 11, `prop:two-families`,
lines 154–181 and 200–207. -/
theorem dyadicNeighborhood_union_iUnion_fineCells_eq_univ (o : ℝ × ℝ)
    (Z : Finset (ℤ × ℤ)) (C k₀ : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C) :
    dyadicNeighborhood o k₀ Z C ∪
      (⋃ k ≥ k₀, ⋃ z ∈ fineLayerIndices o k (fineScaleIndex k) Z C,
        dyadicCell o (fineScaleIndex k) z) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ dyadicNeighborhood o k₀ Z C
  · exact Set.mem_union_left _ hx
  · obtain ⟨⟨k, z⟩, ⟨hk, hz, hxz⟩, _⟩ :=
      exists_unique_fineCell_of_not_mem_dyadicNeighborhood o Z C k₀ hZ hC x hx
    exact Set.mem_union_right _ (Set.mem_iUnion₂.mpr
      ⟨k, hk, Set.mem_iUnion₂.mpr ⟨z, hz, hxz⟩⟩)

end FineCellPartition

end TNLean.PEPS.AreaLaw.Geometry
