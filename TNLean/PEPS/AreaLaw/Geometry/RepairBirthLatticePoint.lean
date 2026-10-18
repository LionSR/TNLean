/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairCurrentRegions
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank
import TNLean.PEPS.AreaLaw.Geometry.RepairStageSites

/-!
# Lattice points in the births of retained regions

The final assembly of Proposition 11.2 keeps only the identifiers whose final
actual regions meet the cut `A`. A site of `A` is a lattice point, and every
current region lies in its remembered closed birth. Hence the birth of every
such identifier contains a lattice point. Births are retained unchanged under
the inclusion of old identifiers, so the conclusion holds at the generation
where the identifier was born.

This is the lattice-point premise `integerPoint w ∈ …` of
`initialBelt_exists_template` and `repairReplacement_exists_template`. For a
belt tile one takes generation zero, where the remembered birth is the initial
birth region; for a replacement born at generation `j + 1`, one takes that
generation.

## Main statements

* `repairStage_birth_oldInclusion`: births are retained under old-identifier
  inclusions.
* `repairStage_exists_integerPoint_mem_birth`: a current region meeting the cut
  has a lattice point in its birth.
* `repairStage_exists_integerPoint_mem_birth_of_oldInclusion`: the same for the
  birth at an earlier generation, from a later region meeting the cut.
* `repairStage_retained_exists_integerPoint_mem_birth`: the same for the
  retained identifiers.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `10-geometry.tex`: retention of identifiers
  whose final actual regions meet `A`, lines 776–779; remembered closed births
  and current regions, lines 558–561; replacement instructions, lines 398–409.
  The nonemptiness of a template is part of Definition 9.3
  (`scanner:template`, `08-scanner.tex`, lines 546–564).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- Retaining an identifier keeps its remembered birth.
Source: area-law Section 11, lines 398–409 and 558–561. -/
theorem repairStage_birth_oldInclusion (j n : ℕ) (i : (𝔇 j).regionIndex) :
    (𝔇 (j + n)).birth (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) =
      (𝔇 j).birth i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- If the current region of an identifier meets the cut, then its birth
contains a lattice point.
Source: area-law Section 11, lines 558–561 and 776–779. -/
theorem repairStage_exists_integerPoint_mem_birth (j : ℕ) (i : (𝔇 j).regionIndex)
    (hi : ((𝔇 j).regionSites Λ A i).Nonempty) :
    ∃ w : ℤ × ℤ, integerPoint w ∈ (𝔇 j).birth i := by
  classical
  obtain ⟨y, hy⟩ := hi
  exact ⟨y.val, repairStage_current_subset_birth o Λ A C k₀ hC h₀ Sstar j i
    (Finset.mem_filter.mp hy).2⟩

/-- If an identifier of generation `j`, retained to generation `j + n`, has a
current region meeting the cut there, then its birth at generation `j` contains
a lattice point. With `j = 0` this is the premise of the belt template; with a
replacement of generation `j` it is the premise of the replacement template.
Source: area-law Section 11, lines 398–409, 558–561 and 776–779. -/
theorem repairStage_exists_integerPoint_mem_birth_of_oldInclusion (j n : ℕ)
    (i : (𝔇 j).regionIndex)
    (hi : ((𝔇 (j + n)).regionSites Λ A
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i)).Nonempty) :
    ∃ w : ℤ × ℤ, integerPoint w ∈ (𝔇 j).birth i :=
  repairStage_birth_oldInclusion o Λ A C k₀ hC h₀ Sstar j n i ▸
    repairStage_exists_integerPoint_mem_birth o Λ A C k₀ hC h₀ Sstar (j + n) _ hi

/-- Every retained identifier, that is every non-dummy identifier whose current
region meets the cut, has a lattice point in its birth.
Source: area-law Section 11, lines 558–561 and 776–779. -/
theorem repairStage_retained_exists_integerPoint_mem_birth (j : ℕ)
    (i : (𝔇 j).RetainedRegionIndex Λ A) :
    ∃ w : ℤ × ℤ, integerPoint w ∈ (𝔇 j).birth i.val :=
  repairStage_exists_integerPoint_mem_birth o Λ A C k₀ hC h₀ Sstar j i.val i.property.2

end TNLean.PEPS.AreaLaw.Geometry
