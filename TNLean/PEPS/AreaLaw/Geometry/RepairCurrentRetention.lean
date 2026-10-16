/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank

/-!
# Decrease of retained current regions

The current region of a retained identifier decreases at each repair step.
No metric estimate or termination assumption is needed: each old region loses
the common removal union.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 398–409,
and comparison with earlier actual regions, lines 584–591.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- Retaining an identifier can only decrease its current region.
Source: area-law Section 11, lines 398–409 and 584–591. -/
theorem repairStage_current_oldInclusion_subset (j n : ℕ)
    (i : (𝔇 j).regionIndex) :
    (𝔇 (j + n)).current
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) ⊆
        (𝔇 j).current i := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih => exact Set.sdiff_subset.trans ih

end TNLean.PEPS.AreaLaw.Geometry
