/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanRadialIncidence
import TNLean.PEPS.AreaLaw.Geometry.FanAffineCoordinates
import Mathlib.Analysis.Convex.Combination

/-!
# Convexity after removing fan radials

Deleting any selected family of radial segments from an elementary fan
triangle preserves convexity. A radial meeting the triangle only at its center
removes that vertex; the two incident radials remove its two radial edges.
Barycentric coordinates express each deletion as the intersection of the
triangle with a strict affine half-plane. Intersections give the statement for
an arbitrary selected family. An empty family retains the entire triangle.

The affine basis and the radial-incidence classification are derived from the
actual fan geometry. The origin, dyadic exponent, signed cell index, optional
midpoint subdivisions and selected family are arbitrary.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–363.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Auxiliary centre-face classification for area-law Section 11,
`geometry:initial-stars`, lines 352–363. The affine basis is derived from
actual fan regularity before applying this fact to a fan triangle. -/
private theorem center_zero_coord_iff (B : AffineBasis (Fin 3) ℝ (ℝ × ℝ))
    (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ (Set.range B)) :
    x = B 0 ↔ B.coord 1 x + B.coord 2 x = 0 := by
  have hnonneg : ∀ i : Fin 3, 0 ≤ B.coord i x := by
    simpa only [B.convexHull_eq_nonneg_coord, Set.mem_ofPred_eq] using hx
  constructor
  swap
  · have hzero_coords : B.coord 1 x + B.coord 2 x = 0 →
        B.coord 1 x = 0 ∧ B.coord 2 x = 0 :=
      (add_eq_zero_iff_of_nonneg (hnonneg 1) (hnonneg 2)).mp
    refine fun hzero ↦ B.ext_elem (fun i ↦ ?_)
    have hcoord0 : B.coord 0 x = 1 := by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two, add_zero, hzero] using
        B.sum_coord_apply_eq_one x
    fin_cases i
    all_goals simp [hcoord0,
      (hzero_coords hzero).1, (hzero_coords hzero).2]
  · rintro rfl
    simp

/-- A closed face of the triangle is the zero set of its omitted coordinate.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 352–363.
The actual fan basis is derived from regularity, rather than supplied to the
source-facing convexity theorem. -/
private theorem face_zero_coord_iff (B : AffineBasis (Fin 3) ℝ (ℝ × ℝ))
    (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ (Set.range B)) (j : Fin 3) :
    x ∈ convexHull ℝ ((B : Fin 3 → ℝ × ℝ) '' ({j}ᶜ : Set (Fin 3))) ↔
      B.coord j x = 0 := by
  let S : Affine.Simplex ℝ (ℝ × ℝ) 2 := ⟨B, B.ind⟩
  have hcard : ({j}ᶜ : Finset (Fin 3)).card = 1 + 1 := by simp [Finset.card_compl]
  have hface := S.affineCombination_mem_closedInterior_face_iff_nonneg hcard
    (B.sum_coord_apply_eq_one x)
  rw [← (S.face hcard).convexHull_eq_closedInterior, S.range_face_points] at hface
  simp only [S, B.affineCombination_coord_eq_self, Finset.coe_compl,
    Finset.coe_singleton] at hface
  have hnonneg : ∀ i : Fin 3, 0 ≤ B.coord i x := by
    simpa only [B.convexHull_eq_nonneg_coord, Set.mem_ofPred_eq] using hx
  simpa [hnonneg] using hface

/-- Removing a closed face of the triangle imposes positivity of its omitted
coordinate. Auxiliary to area-law Section 11, `geometry:initial-stars`,
lines 352–363. -/
private theorem sdiff_face_eq_inter_coord_pos (B : AffineBasis (Fin 3) ℝ (ℝ × ℝ))
    (j : Fin 3) :
    convexHull ℝ (Set.range B) \
      convexHull ℝ ((B : Fin 3 → ℝ × ℝ) '' ({j}ᶜ : Set (Fin 3))) =
      convexHull ℝ (Set.range B) ∩ {x | 0 < B.coord j x} := by
  ext x
  by_cases hx : x ∈ convexHull ℝ (Set.range B)
  · have hnonneg : ∀ i : Fin 3, 0 ≤ B.coord i x := by
      simpa only [B.convexHull_eq_nonneg_coord, Set.mem_ofPred_eq] using hx
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, hx, true_and,
      face_zero_coord_iff B x hx j]
    exact ⟨fun hzero ↦ lt_of_le_of_ne (hnonneg j) (Ne.symm hzero), ne_of_gt⟩
  · simp only [Set.mem_sdiff, Set.mem_inter_iff, hx, false_and]

/-- Removing any one closed face from the triangle preserves convexity.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 352–363. -/
private theorem convex_sdiff_face (B : AffineBasis (Fin 3) ℝ (ℝ × ℝ)) (j : Fin 3) :
    Convex ℝ (convexHull ℝ (Set.range B) \
      convexHull ℝ ((B : Fin 3 → ℝ × ℝ) '' ({j}ᶜ : Set (Fin 3)))) := by
  rw [sdiff_face_eq_inter_coord_pos B j]
  exact (convex_convexHull ℝ (Set.range B)).inter
    (Convex.affine_preimage (B.coord j) (convex_Ioi (𝕜 := ℝ) (0 : ℝ)))

/-- Removing the centre vertex imposes positivity of the sum of the other
coordinates. Auxiliary to area-law Section 11, `geometry:initial-stars`,
lines 352–363. -/
private theorem sdiff_center_eq_inter_sum_coord_pos (B : AffineBasis (Fin 3) ℝ (ℝ × ℝ)) :
    convexHull ℝ (Set.range B) \ ({B 0} : Set (ℝ × ℝ)) =
      convexHull ℝ (Set.range B) ∩ {x | 0 < B.coord 1 x + B.coord 2 x} := by
  ext x
  by_cases hx : x ∈ convexHull ℝ (Set.range B)
  · have hnonneg : ∀ i : Fin 3, 0 ≤ B.coord i x := by
      simpa only [B.convexHull_eq_nonneg_coord, Set.mem_ofPred_eq] using hx
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, hx, true_and, center_zero_coord_iff B x hx]
    exact ⟨fun hzero ↦ lt_of_le_of_ne (add_nonneg (hnonneg 1) (hnonneg 2))
      (Ne.symm hzero), ne_of_gt⟩
  · simp only [Set.mem_sdiff, Set.mem_inter_iff, hx, false_and]

/-- Removing the centre vertex preserves convexity of the triangle.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 352–363. -/
private theorem convex_sdiff_center (B : AffineBasis (Fin 3) ℝ (ℝ × ℝ)) :
    Convex ℝ (convexHull ℝ (Set.range B) \ ({B 0} : Set (ℝ × ℝ))) := by
  rw [sdiff_center_eq_inter_sum_coord_pos B]
  exact (convex_convexHull ℝ (Set.range B)).inter
    (Convex.affine_preimage (B.coord 1 + B.coord 2)
      (convex_Ioi (𝕜 := ℝ) (0 : ℝ)))


/-- Removing an actual fan radial from a fan triangle preserves convexity.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 352–363,
at source revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem cellFanPolygon_sdiff_radial_convex (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i t : CellFanSlot split) :
    Convex ℝ ((cellFanPolygon o ℓ z split i).region \
      segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split t)) := by
  obtain ⟨B, hB⟩ := cellFanPolygon_exists_affineBasis o ℓ z split i
  have hregion : (cellFanPolygon o ℓ z split i).region =
      convexHull ℝ (Set.range B) := by
    simp only [hB, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
    rfl
  have hvertices : B 0 = cellFanCenter o ℓ z ∧
      B 1 = cellFanStart o ℓ z split i ∧ B 2 = cellFanEnd o ℓ z split i :=
    ⟨congrFun hB 0, congrFun hB 1, congrFun hB 2⟩
  by_cases hti : t ≠ i
  · by_cases hstart : cellFanEnd o ℓ z split t ≠ cellFanStart o ℓ z split i
    · have hcut : (cellFanPolygon o ℓ z split i).region \
          segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split t) =
          (cellFanPolygon o ℓ z split i).region \
            ({cellFanCenter o ℓ z} : Set (ℝ × ℝ)) := by
        ext x
        exact ⟨fun hx ↦ ⟨hx.1, fun hxc ↦ hx.2
          (Set.mem_of_eq_of_mem (Set.mem_singleton_iff.mp hxc)
            (left_mem_segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split t)))⟩,
          fun hx ↦ ⟨hx.1, fun hxt ↦
            ((cellFanPolygon_mem_iff_of_mem_radial o ℓ z split i t x
              (fun hxc ↦ hx.2 (Set.mem_singleton_iff.mpr hxc)) hxt).mp hx.1).elim
              hti hstart⟩⟩
      exact hcut.symm ▸ (hregion.symm ▸
        (hvertices.1 ▸ convex_sdiff_center B))
    · push Not at hstart
      have hindices : ({(2 : Fin 3)}ᶜ : Set (Fin 3)) = {0, 1} :=
        Set.ext (by decide)
      simpa only [hindices, Set.image_pair, convexHull_pair, hvertices.1,
        hvertices.2.1, ← hregion, hstart] using
        convex_sdiff_face B 2
  · push Not at hti
    have hindices : ({(1 : Fin 3)}ᶜ : Set (Fin 3)) = {0, 2} :=
      Set.ext (by decide)
    simpa only [hindices, Set.image_pair, convexHull_pair, hvertices.1,
      hvertices.2.2, ← hregion, hti] using
      convex_sdiff_face B 1


/-- Removing an arbitrary selected family of cuts is the intersection of the
individual deletions within the original set. The outer intersection retains
that set when the selected family is empty.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 333–370, auxiliary set identity for
removing the selected radial segments.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/
private theorem selected_cuts_intersection {α ι : Type*}
    (P : Set α) (A : Set ι) (R : ι → Set α) :
    P \ (⋃ t ∈ A, R t) = P ∩ ⋂ t ∈ A, (P \ R t) := by
  exact Set.ext (fun x ↦ Iff.intro
    (fun hx ↦ And.intro hx.1
      (Set.mem_iInter₂.mpr (fun t ht ↦
        And.intro hx.1 (fun hxt ↦
          hx.2 (Set.mem_iUnion₂.mpr ⟨t, ht, hxt⟩)))))
    (fun hx ↦ And.intro hx.1
      (fun hxu ↦ Exists.elim (Set.mem_iUnion₂.mp hxu) (fun t ht ↦
        Exists.elim ht (fun htA hxt ↦
          (Set.mem_iInter₂.mp hx.2 t htA).2 hxt)))))


/-- Removing any selected family of actual fan radials preserves convexity of
an actual fan triangle, including when no radial is selected.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–363,
at source revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem cellFanPolygon_sdiff_radials_convex (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) (A : Set (CellFanSlot split)) :
    Convex ℝ ((cellFanPolygon o ℓ z split i).region \
      (⋃ t ∈ A, segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split t))) := by
  exact (selected_cuts_intersection (cellFanPolygon o ℓ z split i).region A
    (fun t ↦ segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split t))).symm ▸
      (convex_convexHull ℝ _).inter
        (convex_iInter₂ fun t _ ↦ cellFanPolygon_sdiff_radial_convex o ℓ z split i t)

end TNLean.PEPS.AreaLaw.Geometry
