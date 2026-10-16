/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Set.Lattice.Bounded
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank
import TNLean.PEPS.AreaLaw.Geometry.RepairTermination

/-!
# Retained current regions after an empty repair generation

An empty mark family removes no points. Every retained current region therefore
stays unchanged at each later generation under the canonical old-identifier
inclusions, since every later mark would have an ancestor in the empty family.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, replacement instructions, lines 398–409, termination, lines
538–541, and current regions, lines 558–561. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- An empty mark family has empty removal union.
Source: area-law Section 11, `geometry:trim-radius`, lines 393–399,
and `geometry:repair-induction`, lines 538–541. -/
theorem repairRemovalSet_eq_empty {K : Type*} [IsEmpty K]
    (v : K → ℝ × ℝ) (S : K → ℝ) : repairRemovalSet v S = ∅ := by
  exact Set.iUnion_of_empty _

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- After the mark family has become empty, an old current region is retained
unchanged at the next generation under the canonical inclusion.
Source: area-law Section 11, lines 398–409, 538–541 and 558–561. -/
theorem repairStage_current_oldInclusion_one_of_isEmpty (j : ℕ)
    [IsEmpty (𝔇 j).markIndex] (i : (𝔇 j).regionIndex) :
    (𝔇 (j + 1)).current
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j 1 i) =
        (𝔇 j).current i := by
  change (𝔇 j).current i \ repairRemovalSet (𝔇 j).location (𝔇 j).scale =
    (𝔇 j).current i
  simp only [repairRemovalSet_eq_empty, Set.sdiff_empty]

/-- After an empty mark generation, every retained current region is unchanged at all
later generations under the canonical inclusions. Source: area-law Section 11,
replacement instructions, lines 398–409; termination, lines 538–541; and current
regions, lines 558–561, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem repairStage_current_oldInclusion_of_isEmpty (j n : ℕ)
    [IsEmpty (𝔇 j).markIndex] (i : (𝔇 j).regionIndex) :
    (𝔇 (j + n)).current
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) =
        (𝔇 j).current i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : IsEmpty (𝔇 (j + n)).markIndex :=
      isEmpty_repairStage_markIndex_add o Λ A C k₀ hC h₀ Sstar j n inferInstance
    exact (repairStage_current_oldInclusion_one_of_isEmpty o Λ A C k₀ hC h₀ Sstar
      (j + n) (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i)).trans ih

end TNLean.PEPS.AreaLaw.Geometry
