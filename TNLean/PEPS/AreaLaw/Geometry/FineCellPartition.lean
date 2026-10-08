/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.LayerPartition
import TNLean.PEPS.AreaLaw.Geometry.DyadicScales

/-!
# Unique actual fine-cell assignment outside the dummy region

For a nonempty endpoint set and dilation width at least two, the unique
half-open layer assignment and the exact finer-cell union give
a unique actual fine cell for every point outside the initial neighborhood.
Consequently that neighborhood and all later actual fine cells cover the plane.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 154–181 and 200–207.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

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

end TNLean.PEPS.AreaLaw.Geometry
