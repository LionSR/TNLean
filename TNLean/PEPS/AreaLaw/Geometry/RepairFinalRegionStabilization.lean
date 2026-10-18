/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairFinalRegion
import TNLean.PEPS.AreaLaw.Geometry.RepairStabilization

/-!
# Final regions at an empty generation

If a generation has no remaining repair marks, its current regions persist
at every later generation. Their intersections over all later generations
therefore equal the current regions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, replacement instructions, lines 398–409, and final actual regions,
lines 558–561 and 584–591. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- At a generation with no remaining repair marks, every final region equals
its current region. Source: area-law Section 11, lines 398–409, 558–561 and 584–591. -/
theorem repairFinalRegion_eq_current_of_isEmpty (j : ℕ)
    [IsEmpty (𝔇 j).markIndex] (i : (𝔇 j).regionIndex) :
    repairFinalRegion o Λ A C k₀ hC h₀ Sstar j i = (𝔇 j).current i := by
  simp only [repairFinalRegion, repairRegionLift_eq_oldInclusion,
    repairStage_current_oldInclusion_of_isEmpty, Set.iInter_const]

end TNLean.PEPS.AreaLaw.Geometry
