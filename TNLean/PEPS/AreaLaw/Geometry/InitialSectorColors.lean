/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorAssignment
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInterfaces
import Mathlib.Analysis.Convex.Hull

/-!
# Colors of adjacent actual sectors

Two neighboring triangles in the smaller concentric fan have the same actual
initial color exactly when their assigned initial identifiers agree. The
assignment is the unique one obtained from the actual initial regions. Their
closed decomposition places the common nondegenerate radial segment in both
birth regions, so distinct identifiers have opposite colors by the actual
initial-interface theorem.

The statement concerns actual endpoint adjacency. It makes no identification
of nonadjacent sectors with the same color or identifier.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 361–370, and `prop:two-families`, lines 313–323.
Source file: `build/sections/10-geometry.tex` in
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Actual neighboring fan triangles contain a common radial segment with
distinct endpoints. The distance of the perimeter endpoint from the center
is the positive fan radius. Auxiliary to Section 11, `prop:two-families`,
lines 308–323, and `geometry:initial-stars`, lines 352–370. -/
private theorem exists_shared_radial_segment (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i j : CellFanSlot split)
    (hadj : cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j ∨
      cellFanEnd o ℓ z split j = cellFanStart o ℓ z split i) :
    ∃ e : ℝ × ℝ, cellFanCenter o ℓ z ≠ e ∧
      segment ℝ (cellFanCenter o ℓ z) e ⊆
        (cellFanPolygon o ℓ z split i).region ∩ (cellFanPolygon o ℓ z split j).region := by
  have ordered (i j : CellFanSlot split)
      (h : cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j) :
      cellFanCenter o ℓ z ≠ cellFanEnd o ℓ z split i ∧
        segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split i) ⊆
          (cellFanPolygon o ℓ z split i).region ∩
            (cellFanPolygon o ℓ z split j).region := by
    constructor
    · intro hce
      have hn := norm_sub_cellFanCenter_of_mem_base o ℓ z split i
        (right_mem_segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i))
      rw [← hce, sub_self, norm_zero] at hn
      have hr : 0 < (2 : ℝ) ^ ℓ / 2 := by positivity
      linarith
    · intro x hx
      constructor
      · change x ∈ convexHull ℝ {cellFanCenter o ℓ z, cellFanStart o ℓ z split i,
          cellFanEnd o ℓ z split i}
        exact segment_subset_convexHull (by simp) (by simp) hx
      · change x ∈ convexHull ℝ {cellFanCenter o ℓ z, cellFanStart o ℓ z split j,
          cellFanEnd o ℓ z split j}
        rw [h] at hx
        exact segment_subset_convexHull (by simp) (by simp) hx
  rcases hadj with h | h
  · exact ⟨cellFanEnd o ℓ z split i, (ordered i j h).1, (ordered i j h).2⟩
  · obtain ⟨hne, hsub⟩ := ordered j i h
    exact ⟨cellFanEnd o ℓ z split j, hne, fun x hx ↦ ⟨(hsub hx).2, (hsub hx).1⟩⟩

/-- On actual neighboring sectors, equality of initial colors is equivalent to
equality of their assigned initial identifiers. The unique assignment is
derived from the actual initial-region family. No identification of
nonadjacent sectors is asserted. Source: Section 11, `geometry:initial-stars`,
lines 333–370, especially 361–370, and `prop:two-families`, lines 313–323. -/
theorem initialRegion_sector_assignment_adjacent_colors_eq_iff
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let ℓ := fineScaleIndex k - 5
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (v.1 - r, v.2 - r)
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let σ := Classical.choose
      (exists_unique_initialRegion_sector_assignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv)
    ∀ s t : J,
      (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
          cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∨
        cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) t =
          cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) s) →
      (initialRegionColor o k₀ Z C a b hC h₀ (σ s) =
          initialRegionColor o k₀ Z C a b hC h₀ (σ t) ↔ σ s = σ t) := by
  classical
  dsimp only
  let ℓ := fineScaleIndex k - 5
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (v.1 - r, v.2 - r)
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let σ : J → I := Classical.choose
    (exists_unique_initialRegion_sector_assignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv)
  change ∀ s t : J,
    (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
        cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∨
      cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) t =
        cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) s) →
    (initialRegionColor o k₀ Z C a b hC h₀ (σ s) =
        initialRegionColor o k₀ Z C a b hC h₀ (σ t) ↔ σ s = σ t)
  have hdecomp (i : I) :
      initialBirthRegion o k₀ Z C a b hC h₀ i ∩ Metric.closedBall v r =
        ⋃ s : {s : J // σ s = i},
          (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s.val).region :=
    (Classical.choose_spec
      (exists_unique_initialRegion_sector_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)).1.2 i
  have hsub (s : J) : (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s).region ⊆
      initialBirthRegion o k₀ Z C a b hC h₀ (σ s) := by
    intro x hx
    have h : x ∈ initialBirthRegion o k₀ Z C a b hC h₀ (σ s) ∩
        Metric.closedBall v r := by
      rw [hdecomp (σ s)]
      exact Set.mem_iUnion.mpr ⟨⟨s, rfl⟩, hx⟩
    exact h.1
  intro s t hadj
  constructor
  · intro hcolor
    by_contra hne
    obtain ⟨e, hce, hradial⟩ := exists_shared_radial_segment
      oSmall ℓ (0, 0) (fun _ ↦ true) s t hadj
    have hcolors := initialRegionColor_ne_of_segment_subset_inter o k₀ Z C a b
      hC h₀ (σ s) (σ t) hne (cellFanCenter oSmall ℓ (0, 0)) e hce
      (fun x hx ↦ ⟨hsub s (hradial hx).1, hsub t (hradial hx).2⟩)
    exact hcolors hcolor
  · intro hsame
    rw [hsame]

end TNLean.PEPS.AreaLaw.Geometry
