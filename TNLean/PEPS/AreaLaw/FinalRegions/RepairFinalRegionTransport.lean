/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Set.Lattice.Order
import Mathlib.Order.Monotone.Basic
import TNLean.PEPS.AreaLaw.RepairStages.RepairBirthRank
import TNLean.PEPS.AreaLaw.FinalRegions.RepairFinalRegion
import TNLean.PEPS.AreaLaw.BirthTemplates.BirthSeparationInitial
import TNLean.PEPS.AreaLaw.RepairStages.RepairCharacteristicLength

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

## Birth separation at a common generation

The separation estimates for initial belts and fresh replacements imply a
single estimate at every later generation. The later closed birth is compared
with the final actual region of an earlier or peer identifier of the same
label. At an empty generation this final region is the current region.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `10-geometry.tex`, lines 565–591 and 784–789.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
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
end

end

section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The existing initial-belt and replacement birth-separation estimates hold
at a common generation for every positive-rank identifier, compared with any
distinct nondummy identifier of the same label and no larger birth rank.
The comparison is with the final actual region, including peers of equal
rank. Auxiliary to area-law Section 11, `geometry:birth-separation`,
`10-geometry.tex`, lines 565–591 and 784–789. -/
theorem repairStage_birth_separation_of_rank_le {c₁ : ℝ}
    (hinitial : IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁)
    (hrepair : IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁)
    (N : ℕ) (x y : (𝔇 N).regionIndex)
    (hx : 0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N x)
    (hne : y ≠ x) (hny : y ≠ (𝔇 N).dummy)
    (hrank : repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N y ≤
      repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N x)
    (hcolor : (𝔇 N).color y = (𝔇 N).color x) :
    ∀ p ∈ (𝔇 N).birth x,
      ∀ q ∈ repairFinalRegion o Λ A C k₀ hC h₀ Sstar N y,
        c₁ * repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N x ^
          (Exponents.rho : ℝ) ≤ dist p q := by
  classical
  induction N with
  | zero =>
    rcases x with x | x | ⟨k, z, R⟩
    · exact (Nat.lt_irrefl 0 hx).elim
    · exact (Nat.lt_irrefl 0 hx).elim
    · exact hinitial (.inr (.inr ⟨k, z, R⟩)) y (fineScaleIndex k.val)
        rfl hne hny hcolor
  | succ N ih =>
    rcases x with x | x
    · rcases y with y | y
      · refine fun p hp q hq ↦
          ih x y hx (fun h ↦ hne (congrArg Sum.inl h))
            (fun h ↦ hny (congrArg Sum.inl h)) hrank hcolor p hp q ?_
        exact (repairFinalRegion_eq_final_oldInclusion
          o Λ A C k₀ hC h₀ Sstar N 1 y).symm ▸ hq
      · have hbound : ∀ (j : ℕ) (i : (𝔇 j).regionIndex),
            repairStageBirthRank o Λ A C k₀ hC h₀ Sstar j i ≤ j + 1 := by
          refine Nat.rec ?_ ?_
          · rintro (i | i | i) <;>
              simp [repairStageBirthRank, initialRegionBirthRank]
          · intro j hj i
            rcases i with i | i
            · exact (hj i).trans (Nat.le_succ _)
            · exact le_rfl
        exact False.elim ((Nat.not_succ_le_self (N + 1))
          (hrank.trans (hbound N x)))
    · exact hrepair N (.inr x) y x.2.1.val rfl hne hcolor

end TNLean.PEPS.AreaLaw.Geometry

end
