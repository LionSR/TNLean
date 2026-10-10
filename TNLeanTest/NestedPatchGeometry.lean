/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.NestedPatches

/-! # Closed boundaries, clipping, disconnected domains, and nested-crossing regressions -/

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry

namespace NestedPatchGeometryTest

private def domain : Finset (ℤ × ℤ) := {(-2, -1), (-1, -1), (0, 0), (7, 1), (8, 1), (100, 100)}

private def leftSite : Site domain := ⟨(7, 1), by simp [domain]⟩

private def rightSite : Site domain := ⟨(8, 1), by simp [domain]⟩

private def negativeSite : Site domain := ⟨(-2, -1), by simp [domain]⟩

private theorem neighbors : (domainGraph domain).Adj leftSite rightSite := by
  norm_num [domainGraph, leftSite, rightSite]

-- Closed squares include equality, including fractional negative centers.
example : negativeSite ∈ closedSquareSample domain (-3 / 2, -1 / 2) (1 / 2) := by
  norm_num [mem_closedSquareSample, negativeSite]

example : negativeSite ∉ closedSquareSample domain (-3 / 2, -1 / 2) (1 / 4) := by
  norm_num [mem_closedSquareSample, negativeSite]

example : negativeSite ∈ closedSquareSample domain (-2, -1) 0 := by
  norm_num [mem_closedSquareSample, negativeSite]

-- The edge crosses when the first endpoint lies exactly on the boundary.
example : s(leftSite, rightSite) ∈ edgeBoundary domain (closedSquareSample domain (0, 0) 7) := by
  rw [mem_edgeBoundary_closedSquareSample_iff neighbors]
  norm_num [squareRadius, leftSite, rightSite]

-- At the second endpoint's radius both endpoints are inside: the interval is right-open.
example : s(leftSite, rightSite) ∉ edgeBoundary domain (closedSquareSample domain (0, 0) 8) := by
  rw [mem_edgeBoundary_closedSquareSample_iff neighbors]
  norm_num [squareRadius, leftSite, rightSite]

example : s(leftSite, rightSite) ∉ edgeBoundary domain (closedSquareSample domain (0, 0) 6) := by
  rw [mem_edgeBoundary_closedSquareSample_iff neighbors]
  norm_num [squareRadius, leftSite, rightSite]

-- A genuine fractional-center crossing in a clipped, disconnected finite domain.
private theorem middle_crossing :
    s(leftSite, rightSite) ∈ edgeBoundary domain (nestedPatch domain (5 / 4, 3 / 2) 4 1) := by
  unfold nestedPatch
  rw [mem_edgeBoundary_closedSquareSample_iff neighbors]
  norm_num [squareRadius, nestedPatchRadius, leftSite, rightSite]

example : Disjoint s(leftSite, rightSite).toFinset (nestedPatch domain (5 / 4, 3 / 2) 4 0) :=
  nestedPatch_crossing_disjoint_earlier middle_crossing (by omega)

example : s(leftSite, rightSite).toFinset ⊆ nestedPatch domain (5 / 4, 3 / 2) 4 2 :=
  nestedPatch_crossing_subset_later middle_crossing (by omega)

example {j : ℕ}
    (h : s(leftSite, rightSite) ∈ edgeBoundary domain (nestedPatch domain (5 / 4, 3 / 2) 4 j)) :
    j = 1 := nestedPatch_crossing_unique h middle_crossing

-- Empty physical domains stay empty, for every real radius and center.
example (c : ℝ × ℝ) (r : ℝ) : closedSquareSample ∅ c r = ∅ := by
  apply Finset.ext
  intro x
  exact (Finset.notMem_empty x.val x.property).elim

-- A nonempty physical domain can have an empty sample at a fractional center.
example : closedSquareSample {(0, 0)} (1 / 2, 1 / 2) (1 / 4) = ∅ := by
  apply Finset.ext
  intro x
  have hx : x.val = (0, 0) := Finset.mem_singleton.mp x.property
  simp only [mem_closedSquareSample, Finset.notMem_empty, iff_false]
  norm_num [hx]

-- Repeated clipped patches need not be distinct even though their radii are distinct.
private theorem singleton_sample (r : ℝ) (hr : 0 ≤ r) :
    closedSquareSample {(0, 0)} (0, 0) r = Finset.univ := by
  apply Finset.ext
  intro x
  have hx : x.val = (0, 0) := Finset.mem_singleton.mp x.property
  simp only [mem_closedSquareSample, Finset.mem_univ, iff_true]
  simpa [hx] using And.intro hr hr

example : nestedPatch {(0, 0)} (0, 0) 4 0 = nestedPatch {(0, 0)} (0, 0) 4 2 := by
  unfold nestedPatch
  rw [singleton_sample _ (by norm_num [nestedPatchRadius]),
    singleton_sample _ (by norm_num [nestedPatchRadius])]

example : edgeBoundary {(0, 0)} (closedSquareSample {(0, 0)} (0, 0) 0) = ∅ := by
  rw [singleton_sample _ le_rfl, edgeBoundary_univ]

-- The additive four remains valid at zero radius, without a connectedness hypothesis.
example (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) :
    ((edgeBoundary Λ (closedSquareSample Λ c 0)).card : ℝ) ≤ 4 := by
  simpa using card_edgeBoundary_closedSquareSample_le Λ c (r := 0) le_rfl

example : nestedPatchCount 4 = 3 := by norm_num [nestedPatchCount]

example : nestedPatchRadius 4 2 = 8 := by norm_num [nestedPatchRadius]

-- The scalar estimate does not silently require nonnegative kappa.
example (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) :
    ∑ j : Fin (nestedPatchCount 4),
      ((edgeBoundary Λ (nestedPatch Λ c 4 j)).card : ℝ) *
        ((-2 : ℝ) / (nestedPatchCount 4 : ℝ)) ^ 2 ≤ 144 := by
  convert sum_card_edgeBoundary_nestedPatch_mul_sq_le Λ c (u := 4) le_rfl (-2) using 1
  norm_num

end NestedPatchGeometryTest
