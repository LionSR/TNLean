/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationInitial
import TNLean.PEPS.AreaLaw.Geometry.RepairCharacteristicLength
import TNLean.PEPS.AreaLaw.Geometry.RepairFinalRegionTransport

/-!
# Birth separation at a common generation

The separation estimates for initial belts and fresh replacements imply a
single estimate at every later generation. The later closed birth is compared
with the final actual region of an earlier or peer identifier of the same
label. At an empty generation this final region is the current region.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `10-geometry.tex`, lines 565–591 and 784–789.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
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
