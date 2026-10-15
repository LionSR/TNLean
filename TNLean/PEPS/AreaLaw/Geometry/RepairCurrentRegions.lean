/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStage

/-!
# Current regions and closed removal sets

At each repair generation, the current region of an identifier lies in its
remembered closed birth. Initially and for fresh replacements, the current
region is the interior of that birth. An old current region only loses the
closed removal squares, while its remembered birth is retained. A finite
mark family gives a closed union of removal squares.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, initial regions, lines 172–177, 212–218 and
313–316; replacement instructions, lines 393–417; and remembered closed
births and current open regions, lines 558–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The removal set of a finite family of marks is closed.
Source: area-law Section 11, `geometry:trim-radius`, lines 393–399. -/
theorem isClosed_repairRemovalSet {K : Type*} [Finite K]
    (v : K → ℝ × ℝ) (S : K → ℝ) : IsClosed (repairRemovalSet v S) := by
  exact isClosed_iUnion_of_finite (fun _ ↦ Metric.isClosed_closedBall)

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- Every actual current region is contained in its remembered birth.
Source: area-law Section 11, lines 172–177, 212–218, 313–316,
393–417 and 558–561. -/
theorem repairStage_current_subset_birth (j : ℕ) (i : (𝔇 j).regionIndex) :
    (𝔇 j).current i ⊆ (𝔇 j).birth i := by
  exact Nat.rec
    (motive := fun j ↦ ∀ i : (𝔇 j).regionIndex, (𝔇 j).current i ⊆ (𝔇 j).birth i)
    (fun _ ↦ interior_subset)
    (fun j ih i ↦ Sum.casesOn i
      (fun x ↦ fun _ hx ↦ ih x hx.1)
      (fun _ ↦ interior_subset)) j i

end TNLean.PEPS.AreaLaw.Geometry
