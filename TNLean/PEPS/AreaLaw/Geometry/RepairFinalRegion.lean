/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationRepair
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank

/-!
# Canonical retention of identifiers in final regions

The retained identifiers used to define final regions agree with the canonical
old-region inclusions. This identifies the two existing descriptions of the
same retention operation without adding another family of maps or regions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 398–409,
and final actual regions, lines 558–561 and 584–591.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The retention map in the final-region intersection is the canonical
inclusion of old identifiers.
Source: area-law Section 11, lines 398–409 and 558–561. -/
theorem repairRegionLift_eq_oldInclusion (j n : ℕ) (i : (𝔇 j).regionIndex) :
    repairRegionLift o Λ A C k₀ hC h₀ Sstar j n i =
      repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Sum.inl ih

end TNLean.PEPS.AreaLaw.Geometry
