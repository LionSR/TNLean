/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularCellGeometry
import TNLean.PEPS.Approximation.AngularInformationBound
import TNLean.PEPS.Approximation.InformationReset

/-!
# Geometric identities for angular information decay

A selected ambient cell retains its clearance on its closure. Membership in
the union of selected cells is determined by the unique grid-cell index.
For physical lattice sites, the real maximum metric equals the integer sup
distance used by the information reset.

Source: polynomial-PEPS manuscript, `00-introduction.tex`, lines 21–25,
and `02-information.tex`, Lemma 3.2 (`lem:cell-cmi`), the information
reset (`lem:reset`), and Proposition 3.4 (`prop:angular`),
lines 168–175, 334–353, and 694–745, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation.AngularGrid

/-- The clearance of a selected ambient cell also holds on its closure.
Source: polynomial-PEPS manuscript, `02-information.tex`, lines 168–175 and 711–725. -/
theorem selected_cell_closure_clearance {o : ℝ × ℝ} {s r b : ℝ}
    {A C : Set (ℝ × ℝ)} {i : ℤ × ℤ}
    (hi : touches o s r A i)
    (hclear : ∀ x ∈ selectedRegion o s r A, ∀ y ∈ C, b ≤ dist x y) :
    ∀ x ∈ closure (cell o s i), ∀ y ∈ C, b ≤ dist x y := by
  intro x hx y hy
  exact le_on_closure
    (fun z hz ↦ hclear z ⟨i, hi, hz⟩ y hy)
    continuous_const.continuousOn (continuous_id.dist continuous_const).continuousOn hx

/-- Selection of a point is selection of its unique grid cell.
Source: polynomial-PEPS manuscript, `02-information.tex`, lines 694–725. -/
theorem mem_selectedRegion_iff_touches_owner {o x : ℝ × ℝ} {s r : ℝ}
    {A : Set (ℝ × ℝ)} (hs : 0 < s) :
    x ∈ selectedRegion o s r A ↔ touches o s r A (owner o s x) := by
  constructor
  · rintro ⟨i, hi, hx⟩
    simpa only [owner_eq_of_mem_cell hs hx] using hi
  · intro hx
    exact ⟨_, hx, mem_cell_owner hs⟩

end TNLean.PEPS.Approximation.AngularGrid

namespace TNLean.PEPS.Approximation

/-- The physical site placement preserves the integer sup distance.
Source: polynomial-PEPS manuscript, `00-introduction.tex`, lines 21–25. -/
theorem dist_sitePosition_eq_supDist {L : ℕ} (x y : SquareLatticeVertex L L) :
    dist (sitePosition L x) (sitePosition L y) =
      (AreaLaw.supDist (AreaLaw.rectangleEmbedding x) (AreaLaw.rectangleEmbedding y) : ℝ) := by
  simp only [sitePosition, AreaLaw.supDist, AreaLaw.rectangleEmbedding, Prod.dist_eq,
    Real.dist_eq, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub,
    Int.cast_natCast, add_sub_add_right_eq_sub]

end TNLean.PEPS.Approximation
