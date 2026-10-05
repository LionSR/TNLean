/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.CZXRectangleDensity

/-!
# Actual CZX rectangle support and physical-sign regressions

The tests cover a one-site region, a two-site rectangle meeting both torus
coordinate seams, a forbidden virtual boundary configuration, and a nontrivial
controlled-phase sign on the actual physical on-site operator.
-/

open TNLean.PEPS
open scoped BigOperators Matrix

local instance : Fact (1 < 3) := ⟨by decide⟩
local instance : Fact (2 < 3) := ⟨by decide⟩

example : Module.finrank ℂ (LinearMap.range (openRegionMap (czxPEPS 3 3)
    (torusContiguousRectangle 0 0 1 1))) = 16 := by
  simpa using finrank_range_openRegionMap_czxRectangle
    (width := 3) (height := 3) 0 0 1 1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

example : Module.finrank ℂ (LinearMap.range (openRegionMap (czxPEPS 3 3)
    (torusContiguousRectangle 1 2 2 1))) = 64 := by
  simpa using finrank_range_openRegionMap_czxRectangle
    (width := 3) (height := 3) 1 2 2 1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

example : czxOnSite 3 12 = -1 := by
  rw [czxOnSite_eq_monomial, Matrix.monomial_apply]
  have hflip : czxSiteFlip 12 = 3 := by decide
  have hphase : czxCZExponent 12 = 1 := by decide
  simp [hflip, hphase]

private def forbiddenLegs (i : Fin 4) : Fin 4 :=
  if i = 0 then czxBond (0, 1) else czxBond (0, 0)

private theorem forbiddenLegs_not_boundary (c : Fin 4 → Fin 2) :
    forbiddenLegs ≠ czxBoundaryLegs 4 c := by
  intro he
  have h0 := congrArg (fun f => (czxBond.symm (f 0)).2) he
  have h1 := congrArg (fun f => (czxBond.symm (f 1)).1) he
  simp [forbiddenLegs, czxBoundaryLegs] at h0 h1
  exact (by decide : (1 : Fin 2) ≠ 0) (h0.trans h1.symm)

example (σ : RegionPhysicalConfig (d := 16)
    (torusContiguousRectangle (width := 3) (height := 3) 0 0 1 1)) :
    openRegionWeight (czxPEPS 3 3) (torusContiguousRectangle 0 0 1 1)
      ((czxRectangleCoordinatesEquiv 0 0 1 1 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).symm forbiddenLegs) σ = 0 := by
  by_contra hn
  obtain ⟨c, hc⟩ := czxRectangleBoundaryLabels_mem_range_of_openRegionWeight_ne_zero
    0 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ σ hn
  have he := czxRectangleCoordinatesEquiv_apply (width := 3) (height := 3)
    0 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((czxRectangleCoordinatesEquiv 0 0 1 1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).symm forbiddenLegs)
  rw [Equiv.apply_symm_apply] at he
  exact forbiddenLegs_not_boundary c (he.trans hc)

example : (regionReducedDensity (czxPEPS 3 3)
    (torusContiguousRectangle 0 0 1 1)).rank = 16 := by
  simpa using rank_regionReducedDensity_czxRectangle
    (width := 3) (height := 3) 0 0 1 1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

example :
    let ρ := regionReducedDensity (czxPEPS 3 3) (torusContiguousRectangle 1 2 2 1)
    (ρ.trace⁻¹ • ρ).rank = 64 := by
  simpa using rank_normalizedRegionReducedDensity_czxRectangle
    (width := 3) (height := 3) 1 2 2 1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

example : (regionReducedDensity (czxPEPS 3 3)
    (torusContiguousRectangle 1 1 2 2)).trace ≠ 0 :=
  trace_regionReducedDensity_czxRectangle_ne_zero
    (width := 3) (height := 3) 1 1 2 2 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

section AxiomChecks
set_option linter.hashCommand false
/-- info: 'TNLean.PEPS.finrank_range_openRegionMap_czxRectangle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finrank_range_openRegionMap_czxRectangle

/-- info: 'TNLean.PEPS.regionPhysicalMap_czxRectangleBoundaryMatrix_column' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionPhysicalMap_czxRectangleBoundaryMatrix_column
/-- info: 'TNLean.PEPS.range_regionReducedDensity_czxRectangle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms range_regionReducedDensity_czxRectangle

/-- info: 'TNLean.PEPS.rank_normalizedRegionReducedDensity_czxRectangle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rank_normalizedRegionReducedDensity_czxRectangle
end AxiomChecks
