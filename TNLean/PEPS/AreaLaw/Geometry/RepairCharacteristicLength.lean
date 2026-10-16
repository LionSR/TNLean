/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStage

/-!
# Characteristic lengths remembered at birth

An initial primary has its layer length r, an initial belt region has its
cell side u, and a replacement has the half-side u of its removal square.
These lengths are retained when an old identifier passes to a later stage.
For a replacement, the scanner template uses primitive scale 2u.

The dummy is assigned zero for totality and is excluded from the retained
physical identifiers. The order of identifiers is determined separately by
their initial class and generation of birth.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:primary-scale`, lines 709–721;
belt and replacement scanner scales, lines 732–740; and the ordering
preceding `geometry:birth-separation`, lines 565–568.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The characteristic length of an initial identifier: r = 2^k for a
primary and u = t_k for a belt region. The primary length is the layer
length; the whole primary can have a larger pitch diameter. The dummy
has value zero for totality and is excluded from retained identifiers.
Source: area-law Section 11, `geometry:primary-scale`, lines 709–721;
initial belt scale, lines 732–734; and dummy exclusion, lines 565–568. -/
def initialRegionCharacteristicLength (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    InitialRegionIndex o k₀ Z C a b hC h₀ → ℝ
  | .inl _ => 0
  | .inr (.inl ⟨k, _⟩) => (2 : ℝ) ^ k.val
  | .inr (.inr ⟨k, _, _⟩) => (2 : ℝ) ^ fineScaleIndex k.val

/-- The characteristic birth length in the actual repair family. Old
identifiers keep their value, and a fresh replacement receives the removal
half-side u computed from its parent scale at birth. Its scanner template
has primitive scale 2u. The initial identifiers use the same joint choice
as the actual initial stage.
Source: area-law Section 11, replacement creation, lines 398–409;
`geometry:primary-scale`, lines 709–721; and belt and replacement scanner
scales, lines 732–740. -/
def repairStageCharacteristicLength (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) :
    (j : ℕ) → (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex → ℝ :=
  Nat.rec
    (motive := fun j ↦
      (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex → ℝ)
    (let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
        o Λ A C k₀ hC h₀
      let a := Classical.choose h
      let hb := Classical.choose_spec h
      let b := Classical.choose hb
      initialRegionCharacteristicLength o k₀ (boundaryEndpoints Λ A) C a b hC h₀)
    (fun j length ↦ fun
      | .inl i => length i
      | .inr q =>
        repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale q.2.1.val))

end TNLean.PEPS.AreaLaw.Geometry
