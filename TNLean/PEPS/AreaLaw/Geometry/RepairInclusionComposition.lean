/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank

/-!
# Coherence of retained current regions across generations

Retaining an identifier over two successive intervals gives the same current
region as retaining it over their combined interval. This equality of subsets
compares the existing canonical inclusions without identifying their dependent
codomain types.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, replacement instructions, lines 398–409, and current regions,
lines 558–561. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The current region obtained by retaining an identifier over a combined
interval equals the current region obtained over the two successive intervals.
No mark-emptiness assumption is required. Source: area-law Section 11,
lines 398–409 and 558–561. -/
theorem repairStage_current_oldInclusion_add (j n m : ℕ) (i : (𝔇 j).regionIndex) :
    (𝔇 (j + (n + m))).current
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j (n + m) i) =
        (𝔇 ((j + n) + m)).current
          (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar (j + n) m
            (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    exact congrArg₂ (fun U V : Set (ℝ × ℝ) ↦ U \ V) ih
      (congrArg (fun t ↦ repairRemovalSet (𝔇 t).location (𝔇 t).scale)
        (Nat.add_assoc j n m).symm)

end TNLean.PEPS.AreaLaw.Geometry
