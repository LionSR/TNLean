/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStage

/-!
# Retained identifiers and the order of birth

Each repair stage retains the old identifiers and adjoins the new replacement
identifiers. Iterating these inclusions compares an identifier at its birth
with the same identifier at a later stage. The natural-number rank places
primaries before initial belt regions and replacements in their generation
order. Identifiers born in the same class have the same rank.

The dummy is assigned rank zero so that the rank is defined on every
identifier. It remains excluded from the order on physical tile identifiers.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 398–409,
and the ordering preceding `geometry:birth-separation`, lines 565–571.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Initial primaries have rank zero and initial belt regions have rank one.
The dummy has rank zero for totality and is excluded from the physical order.
Source: area-law Section 11, ordering preceding `geometry:birth-separation`,
lines 565–568. -/
def initialRegionBirthRank (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    InitialRegionIndex o k₀ Z C a b hC h₀ → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr _) => 1

/-- The canonical inclusion of an old identifier into the next repair stage.
Source: area-law Section 11, lines 398–407, and
`geometry:birth-separation`, lines 584–591. -/
def repairNextOldInclusion (j : ℕ) (Sstar : ℝ) (D : RepairStage) :
    D.regionIndex → (repairNextStage j Sstar D).regionIndex :=
  Sum.inl

/-- The canonical inclusion from generation j to generation j + l, obtained
by retaining the old identifier at each intervening step.
Source: area-law Section 11, lines 398–409, and the ordering preceding
`geometry:birth-separation`, lines 565–571. -/
def repairStageOldInclusion (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) (j : ℕ) :
    (l : ℕ) → (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex →
      (repairStage o Λ A C k₀ hC h₀ Sstar (j + l)).regionIndex :=
  Nat.rec
    (motive := fun l ↦
      (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex →
        (repairStage o Λ A C k₀ hC h₀ Sstar (j + l)).regionIndex)
    (fun i ↦ i)
    (fun l inclusion i ↦
      repairNextOldInclusion (j + l) Sstar
        (repairStage o Λ A C k₀ hC h₀ Sstar (j + l)) (inclusion i))

/-- Birth rank in the actual repair family. Initial ranks are inherited from
the same jointly chosen initial identifiers. Old identifiers retain their
rank, and a replacement born at step j receives rank j + 2.
Source: area-law Section 11, lines 404–409, and the ordering preceding
`geometry:birth-separation`, lines 565–568. -/
def repairStageBirthRank (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) :
    (j : ℕ) → (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex → ℕ :=
  Nat.rec
    (motive := fun j ↦
      (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex → ℕ)
    (let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
        o Λ A C k₀ hC h₀
      let a := Classical.choose h
      let hb := Classical.choose_spec h
      let b := Classical.choose hb
      initialRegionBirthRank o k₀ (boundaryEndpoints Λ A) C a b hC h₀)
    (fun j rank ↦ fun
      | .inl i => rank i
      | .inr _ => j + 2)

end TNLean.PEPS.AreaLaw.Geometry
