/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanRunContacts
import Mathlib.Analysis.Convex.Topology

/-!
# Primitive boundaries of an actual fan

The frontier of each actual fan triangle lies on the outer square frontier
or on an actual radial segment. The finite closed-cover argument and closed
triangle argument are shared with initial lattice boundary avoidance.
The conclusion retains the actual endpoints and hence their scale; it does
not impose a late layer, mesh or contact hypothesis.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323,
and `geometry:initial-stars`, lines 333–370, especially 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The frontier of a finite closed-cover member lies on the outer boundary
or meets another member. Auxiliary to area-law Section 11, `prop:two-families`,
lines 308–323 and 545–559. -/
theorem finiteCover_frontier_subset {ι : Type*} [Finite ι]
    (Q : Set (ℝ × ℝ)) (P : ι → Set (ℝ × ℝ)) (hclosed : ∀ i, IsClosed (P i))
    (hcover : (⋃ i, P i) = closure Q) (i : ι) :
    frontier (P i) ⊆ frontier Q ∪ ⋃ j : {j : ι // j ≠ i}, P i ∩ P j.val := by
  classical
  intro x hx
  have hxi : x ∈ P i := (hclosed i).frontier_subset hx
  by_cases hxQ : x ∈ frontier Q
  · exact Or.inl hxQ
  right
  by_cases hother : ∃ j, j ≠ i ∧ x ∈ P j
  · obtain ⟨j, hji, hxj⟩ := hother
    exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hxi, hxj⟩
  have hxclosed : x ∈ closure Q := hcover ▸ Set.mem_iUnion.mpr ⟨i, hxi⟩
  have hxint : x ∈ interior Q := by
    rw [← closure_sdiff_frontier Q]
    exact ⟨hxclosed, hxQ⟩
  let T : Set (ℝ × ℝ) := ⋃ j : {j : ι // j ≠ i}, P j.val
  have hT : IsClosed T := isClosed_iUnion_of_finite fun j ↦ hclosed j.val
  have hxnot : x ∉ T := by
    intro hxT
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxT
    exact hother ⟨j.val, j.property, hxj⟩
  have hsub : interior Q ∩ Tᶜ ⊆ P i := by
    intro y hy
    have hyclosed : y ∈ closure Q := subset_closure (interior_subset hy.1)
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp (hcover.symm ▸ hyclosed)
    by_cases hji : j = i
    · exact hji ▸ hyj
    · exact False.elim (hy.2 (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩))
  have hxin : x ∈ interior (P i) :=
    interior_maximal hsub (isOpen_interior.inter hT.isOpen_compl) ⟨hxint, hxnot⟩
  exact False.elim ((mem_frontier_iff_notMem_interior hxi).mp hx hxin)

/-- An actual fan triangle is a closed finite convex hull.
Auxiliary to area-law Section 11, `prop:two-families`, lines 308–316 and 545–559. -/
private theorem fan_polygon_isClosed (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    IsClosed (cellFanPolygon o ℓ z split i).region := by
  change IsClosed (convexHull ℝ {cellFanCenter o ℓ z,
    cellFanStart o ℓ z split i, cellFanEnd o ℓ z split i})
  exact (((Set.finite_singleton (cellFanEnd o ℓ z split i)).insert
    (cellFanStart o ℓ z split i)).insert (cellFanCenter o ℓ z)).isClosed_convexHull ℝ

/-- Every actual fan-triangle boundary point lies on the outer cell boundary
or an actual radial segment. Source: Section 11, `prop:two-families`,
lines 299–323, and `geometry:initial-stars`, lines 333–370. -/
theorem cellFanPolygon_frontier_subset_outer_and_radials (o : ℝ × ℝ)
    (ℓ : ℕ) (z : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split) :
    frontier (cellFanPolygon o ℓ z split i).region ⊆
      frontier (dyadicCell o ℓ z) ∪ ⋃ j : CellFanSlot split,
        segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split j) := by
  intro x hx
  rcases finiteCover_frontier_subset (dyadicCell o ℓ z)
      (fun j ↦ (cellFanPolygon o ℓ z split j).region)
      (fan_polygon_isClosed o ℓ z split) (cellFanPolygons_cover o ℓ z split) i hx with
    hxcell | hxother
  · exact Or.inl hxcell
  right
  obtain ⟨⟨j, hji⟩, hinter⟩ := Set.mem_iUnion.mp hxother
  by_cases hxc : x = cellFanCenter o ℓ z
  · subst x
    exact Set.mem_iUnion.mpr ⟨i, left_mem_segment ℝ _ _⟩
  have hc : cellFanCenter o ℓ z ∈ (cellFanPolygon o ℓ z split i).region ∩
      (cellFanPolygon o ℓ z split j).region := by
    rw [cellFanPolygons_inter_eq]
    exact Or.inl rfl
  have hcontact := Set.nontrivial_of_mem_mem_ne hinter hc hxc
  rcases cellFanPolygons_nontrivial_inter_cases o ℓ z split i j hji.symm hcontact with
    ⟨_, heq⟩ | ⟨_, heq⟩
  · exact Set.mem_iUnion.mpr ⟨i, heq ▸ hinter⟩
  · exact Set.mem_iUnion.mpr ⟨j, heq ▸ hinter⟩

end TNLean.PEPS.AreaLaw.Geometry
