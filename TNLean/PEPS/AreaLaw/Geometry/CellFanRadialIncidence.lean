/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanRays
import TNLean.PEPS.AreaLaw.Geometry.FanRunContacts
import Mathlib.Analysis.Convex.Between

/-!
# Noncentral radial incidence in actual cell fans

For every optional midpoint subdivision, a noncentral point on a fan radial lies
in a triangle precisely when the radial ends at that triangle's final endpoint
or its initial endpoint. The proof uses the actual triangle contact
classification and distinctness of the directed endpoint rays.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 352–370.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The unequal-slot direction of noncentral radial incidence for actual fans.
Auxiliary to area-law Section 11, `prop:two-families`, lines 308–323, and
`geometry:initial-stars`, lines 352–370. -/
private theorem cellFanEnd_eq_cellFanStart_of_noncentral_radial_mem_of_ne
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i t : CellFanSlot split) (x : ℝ × ℝ)
    (hxc : x ≠ cellFanCenter o ℓ z)
    (hxt : x ∈ segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split t))
    (hxi : x ∈ (cellFanPolygon o ℓ z split i).region) (hti : t ≠ i) :
    cellFanEnd o ℓ z split t = cellFanStart o ℓ z split i := by
  have hxtP : x ∈ (cellFanPolygon o ℓ z split t).region :=
    segment_subset_convexHull (𝕜 := ℝ)
      (s := ({cellFanCenter o ℓ z, cellFanStart o ℓ z split t,
        cellFanEnd o ℓ z split t} : Set (ℝ × ℝ)))
      (Or.inl rfl) (Or.inr (Or.inr rfl)) hxt
  have hc (s : CellFanSlot split) :
      cellFanCenter o ℓ z ∈ (cellFanPolygon o ℓ z split s).region :=
    subset_convexHull ℝ
      ({cellFanCenter o ℓ z, cellFanStart o ℓ z split s,
        cellFanEnd o ℓ z split s} : Set (ℝ × ℝ)) (Or.inl rfl)
  have hcontact : ((cellFanPolygon o ℓ z split t).region ∩
      (cellFanPolygon o ℓ z split i).region).Nontrivial :=
    Set.nontrivial_of_mem_mem_ne ⟨hxtP, hxi⟩ ⟨hc t, hc i⟩ hxc
  rcases cellFanPolygons_nontrivial_inter_cases o ℓ z split t i hti hcontact with
    ⟨hnext, hinter⟩ | ⟨hback, hinter⟩
  swap
  · have hxiR : x ∈ segment ℝ (cellFanCenter o ℓ z)
        (cellFanEnd o ℓ z split i) :=
      hinter ▸ (show x ∈ (cellFanPolygon o ℓ z split t).region ∩
        (cellFanPolygon o ℓ z split i).region from ⟨hxtP, hxi⟩)
    have hray : SameRay ℝ (cellFanEnd o ℓ z split t - cellFanCenter o ℓ z)
        (cellFanEnd o ℓ z split i - cellFanCenter o ℓ z) :=
      (mem_segment_iff_wbtw.mp hxt).sameRay_vsub_left.symm.trans
        (mem_segment_iff_wbtw.mp hxiR).sameRay_vsub_left
        (fun h0 ↦ (hxc (sub_eq_zero.mp h0)).elim)
    exact (hti ((cellFanEnd_sameRay_iff o ℓ z split t i).mp hray)).elim
  · exact hnext

/-- A noncentral point on an actual fan radial lies in a fan triangle precisely
when it is that triangle's final radial or the radial ending at its start.
Source: area-law Section 11, `prop:two-families`, lines 308–323, and
`geometry:initial-stars`, lines 352–370. -/
theorem cellFanPolygon_mem_iff_of_mem_radial (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i t : CellFanSlot split) (x : ℝ × ℝ)
    (hxc : x ≠ cellFanCenter o ℓ z)
    (hxt : x ∈ segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split t)) :
    x ∈ (cellFanPolygon o ℓ z split i).region ↔
      t = i ∨ cellFanEnd o ℓ z split t = cellFanStart o ℓ z split i := by
  constructor
  swap
  · rintro (rfl | hstart)
    swap
    · rw [hstart] at hxt
      exact segment_subset_convexHull (𝕜 := ℝ)
        (s := ({cellFanCenter o ℓ z, cellFanStart o ℓ z split i,
          cellFanEnd o ℓ z split i} : Set (ℝ × ℝ)))
        (Or.inl rfl) (Or.inr (Or.inl rfl)) hxt
    · exact segment_subset_convexHull (𝕜 := ℝ)
        (s := ({cellFanCenter o ℓ z, cellFanStart o ℓ z split t,
          cellFanEnd o ℓ z split t} : Set (ℝ × ℝ)))
        (Or.inl rfl) (Or.inr (Or.inr rfl)) hxt
  · exact fun hxi ↦ (eq_or_ne t i).elim Or.inl
      (fun hti ↦ Or.inr
        (cellFanEnd_eq_cellFanStart_of_noncentral_radial_mem_of_ne
          o ℓ z split i t x hxc hxt hxi hti))

end TNLean.PEPS.AreaLaw.Geometry
