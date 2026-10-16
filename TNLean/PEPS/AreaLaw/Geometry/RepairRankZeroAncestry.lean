/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank
import TNLean.PEPS.AreaLaw.Geometry.RepairCharacteristicLength

/-!
# Rank-zero identifiers under retention

The old-identifier inclusions are injective and retain the distinguished
dummy. A fresh replacement always has positive birth rank, so every
rank-zero identifier at a later generation is the retained image of a
rank-zero identifier at each earlier generation. Remembered births, colours,
and characteristic lengths are unchanged by retention. Consequently every
rank-zero identifier other than the dummy comes from one unique original
primary, with the same jointly chosen residues as the actual initial stage.

These are auxiliary consequences of the actual repair definitions in OpenAI,
*A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 11, `10-geometry.tex`, retention and replacement creation,
lines 398–409, and the ordering and dummy exclusion, lines 565–571.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- Retaining old identifiers over any number of generations is injective.
Auxiliary to area-law Section 11, `10-geometry.tex`, retained identifiers,
lines 398–409, and their ordering, lines 565–571. -/
lemma repairStageOldInclusion_injective (j n : ℕ) :
    Function.Injective (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n) := by
  classical
  exact Nat.rec Function.injective_id (fun _ ih ↦ Sum.inl_injective.comp ih) n

/-- The distinguished dummy remains the dummy under the old-identifier inclusion.
Auxiliary to area-law Section 11, `10-geometry.tex`, retention, lines 398–409,
and exclusion of the dummy from the physical order, lines 565–568. -/
lemma repairStageOldInclusion_dummy (j n : ℕ) :
    repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n (𝔇 j).dummy =
      (𝔇 (j + n)).dummy := by
  classical
  exact Nat.rec rfl (fun _ ih ↦ congrArg Sum.inl ih) n

/-- Every rank-zero identifier at generation `j + n` is retained from a
rank-zero identifier at generation `j`. The dummy is included here.
Auxiliary to area-law Section 11, `10-geometry.tex`, retention and fresh
replacement creation, lines 398–409, and the birth order, lines 565–571. -/
lemma exists_repairStageOldInclusion_of_repairStageBirthRank_eq_zero
    (j n : ℕ) (x : (𝔇 (j + n)).regionIndex)
    (hx : repairStageBirthRank o Λ A C k₀ hC h₀ Sstar (j + n) x = 0) :
    ∃ y : (𝔇 j).regionIndex,
      repairStageBirthRank o Λ A C k₀ hC h₀ Sstar j y = 0 ∧
        repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n y = x := by
  classical
  induction n with
  | zero => exact ⟨x, hx, rfl⟩
  | succ n ih =>
    cases x with
    | inl x =>
      obtain ⟨y, hy, hxy⟩ := ih x hx
      exact ⟨y, hy, congrArg Sum.inl hxy⟩
    | inr x => exact Nat.noConfusion hx

/-- Retaining an identifier does not change its remembered closed birth.
Auxiliary to area-law Section 11, `10-geometry.tex`, retention and replacement
creation, lines 398–409, and remembered births, lines 558–561. -/
lemma repairStage_birth_oldInclusion (j n : ℕ) (i : (𝔇 j).regionIndex) :
    (𝔇 (j + n)).birth
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) = (𝔇 j).birth i := by
  classical
  exact Nat.rec rfl (fun _ ih ↦ ih) n

/-- Retaining an identifier preserves its binary label.
Auxiliary to area-law Section 11, `10-geometry.tex`, retention and the labels
of replacement regions, lines 398–409 and 497–504. -/
lemma repairStage_color_oldInclusion (j n : ℕ) (i : (𝔇 j).regionIndex) :
    (𝔇 (j + n)).color
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) = (𝔇 j).color i := by
  classical
  exact Nat.rec rfl (fun _ ih ↦ ih) n

/-- Retaining an identifier preserves its characteristic birth length.
Auxiliary to area-law Section 11, `10-geometry.tex`, retention, lines 398–409,
primary scales, lines 709–721, and belt and replacement scales, lines 732–740. -/
lemma repairStageCharacteristicLength_oldInclusion (j n : ℕ)
    (i : (𝔇 j).regionIndex) :
    repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar (j + n)
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) =
        repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar j i := by
  classical
  exact Nat.rec rfl (fun _ ih ↦ ih) n

/-- A rank-zero identifier other than the dummy is retained from exactly one
original primary. The witness is the existing layer-and-pitch index, using
precisely the joint residues of the actual initial stage. The endpoint is
kept as `0 + n` to use the existing dependent inclusion without a new map.
Auxiliary to area-law Section 11, `10-geometry.tex`, primary identifiers,
lines 212–218, retention, lines 398–409, and birth order with the dummy
excluded, lines 565–571. No finiteness of the ambient primary family is assumed. -/
lemma existsUnique_initialPrimary_of_repairStageBirthRank_eq_zero
    (n : ℕ) (x : (𝔇 (0 + n)).regionIndex)
    (hx : repairStageBirthRank o Λ A C k₀ hC h₀ Sstar (0 + n) x = 0)
    (hxd : x ≠ (𝔇 (0 + n)).dummy) :
    let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
      o Λ A C k₀ hC h₀
    let a := Classical.choose h
    let b := Classical.choose (Classical.choose_spec h)
    ∃! p : (Σ k : {k : ℕ // k₀ ≤ k},
      {J : ℤ × ℤ // J ∈ primaryPitchIndices o k.val (fineScaleIndex k.val)
        (pitchScaleIndex k.val) (boundaryEndpoints Λ A) C (a k.val).val (b k.val).val}),
      repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar 0 n (.inr (.inl p)) = x := by
  classical
  obtain ⟨y, hy, hxy⟩ :=
    exists_repairStageOldInclusion_of_repairStageBirthRank_eq_zero
      o Λ A C k₀ hC h₀ Sstar 0 n x hx
  rcases y with ⟨⟩ | p | q
  · exact False.elim (hxd (hxy.symm.trans
      (repairStageOldInclusion_dummy o Λ A C k₀ hC h₀ Sstar 0 n)))
  · refine ⟨p, hxy, fun q hq ↦ ?_⟩
    exact Sum.inl.inj (Sum.inr.inj
      (repairStageOldInclusion_injective o Λ A C k₀ hC h₀ Sstar 0 n
        (hq.trans hxy.symm)))
  · exact Nat.noConfusion hy

end TNLean.PEPS.AreaLaw.Geometry
