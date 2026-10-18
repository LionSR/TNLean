/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Set.Lattice.Order
import Mathlib.Order.Monotone.Basic
import TNLean.PEPS.AreaLaw.Geometry.RepairCurrentRetention
import TNLean.PEPS.AreaLaw.Geometry.RepairFinalRegionStabilization
import TNLean.PEPS.AreaLaw.Geometry.RepairInclusionComposition

/-!
# Final regions under retention

Canonical retention of an identifier preserves its final actual region:
removing a finite prefix from the decreasing family of its current regions
leaves the intersection unchanged. At a later empty generation, this final
region equals the current region of the retained identifier. Both statements
include a retention interval of length zero. The comparisons use equalities
of subsets rather than equalities between maps with different dependent
codomain types.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 398–409,
final actual regions, lines 558–561, and comparison with earlier actual
regions, lines 584–591. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The final actual region is unchanged under the canonical retention of an
identifier. This includes an interval of length zero and does not require an
empty generation. Auxiliary to area-law Section 11, `10-geometry.tex`,
lines 398–409, 558–561 and 584–591. -/
theorem repairFinalRegion_eq_final_oldInclusion (j n : ℕ) (i : (𝔇 j).regionIndex) :
    repairFinalRegion o Λ A C k₀ hC h₀ Sstar j i =
      repairFinalRegion o Λ A C k₀ hC h₀ Sstar (j + n)
        (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) :=
  let R : ℕ → Set (ℝ × ℝ) := fun m ↦
    (𝔇 (j + m)).current
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j m i)
  let hR : Antitone R := antitone_nat_of_succ_le fun m ↦
    (repairStage_current_oldInclusion_add o Λ A C k₀ hC h₀ Sstar j m 1 i).le.trans
      (repairStage_current_oldInclusion_subset o Λ A C k₀ hC h₀ Sstar (j + m) 1
        (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j m i))
  calc
    repairFinalRegion o Λ A C k₀ hC h₀ Sstar j i = ⋂ m, R m :=
      Set.iInter_congr fun m ↦
        congrArg ((𝔇 (j + m)).current)
          (repairRegionLift_eq_oldInclusion o Λ A C k₀ hC h₀ Sstar j m i)
    _ = ⋂ m, R (m + n) := (hR.iInter_nat_add n).symm
    _ = repairFinalRegion o Λ A C k₀ hC h₀ Sstar (j + n)
        (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) :=
      Set.iInter_congr fun m ↦
        (congrArg R (Nat.add_comm m n)).trans
          ((repairStage_current_oldInclusion_add o Λ A C k₀ hC h₀ Sstar
            j n m i).trans
            (congrArg ((𝔇 ((j + n) + m)).current)
              (repairRegionLift_eq_oldInclusion o Λ A C k₀ hC h₀ Sstar
                (j + n) m
                (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i))).symm)

/-- At a later empty generation, the final region of an earlier identifier
is its current region under the canonical old-identifier inclusion. The case
n = 0 is included. Source: area-law Section 11, lines 398–409, 558–561 and
584–591. -/
theorem repairFinalRegion_eq_current_oldInclusion_of_isEmpty (j n : ℕ)
    [IsEmpty (𝔇 (j + n)).markIndex] (i : (𝔇 j).regionIndex) :
    repairFinalRegion o Λ A C k₀ hC h₀ Sstar j i =
      (𝔇 (j + n)).current
        (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) :=
  (repairFinalRegion_eq_final_oldInclusion o Λ A C k₀ hC h₀ Sstar j n i).trans
    (repairFinalRegion_eq_current_of_isEmpty o Λ A C k₀ hC h₀ Sstar (j + n)
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i))

end TNLean.PEPS.AreaLaw.Geometry
