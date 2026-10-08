/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CorrectedSourceFrames
import TNLean.PEPS.Approximation.SourceGaussianVectorDensity
import TNLean.PEPS.Approximation.CorrectedInputVectorIdentity

/-!
# Corrected endpoint columns in the actual prepared input

The original partial output is obtained by the actual absorbed and reordered
word on the corrected endpoint columns and the unchanged crossing vector.
The common source-free rearrangement is derived from the original positions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-correctedschmidtinput-01
TNLean.PEPS.PairEffect.SourceCircuit.HasCorrectedSchmidtInputs
Provenance-ID: 8769-source-resource-correctedschmidtinput-02
TNLean.PEPS.PairEffect.SourceCircuit.correctedMask_meets
Provenance-ID: 8769-source-resource-correctedschmidtinput-03
TNLean.PEPS.PairEffect.SourceCircuit.exists_correctedSchmidtInput_identity
-/


noncomputable section
open scoped TensorProduct Matrix
namespace TNLean.PEPS.PairEffect.SourceCircuit
open SourceInventory TNLean.PEPS.Approximation
variable {P : Type} {a b : Layout P}
variable (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- Slots prepared in advance retain their original vectors under corrected
endpoint substitution. -/
private theorem fill_partialSchmidtSourceVectors
    (ξ : Choices (correctedMask w S) w)
    (u : PartialSchmidtCoordinates (correctedMask w S) w S) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    fillSourceVectors R U V (correctedFreeSlots w S)
      (fun i _ ↦ partialSlotVector A w ξ i) (partialSchmidtSourceVectors A w S E F ξ u) =
        partialSchmidtSourceVectors A w S E F ξ u := by
  classical
  intro A R U V
  funext i
  unfold fillSourceVectors
  split_ifs with h
  · have hi : i ∉ selectedPartialSlots A w S := by
      intro hi
      have hf := (correctedFreeSlots_eq_true_iff w S i).mpr
        (Or.inl ((mem_selectedPartialSlots A w S i).mp hi))
      simp [h] at hf
    simp only [partialSchmidtSourceVectors, dite_eq_right hi]
  · rfl

/-- Corrected endpoint substitutions leave the exact crossing-source vector unchanged. -/
private theorem crossingVector_partialSchmidtSourceVectors
    (ξ : Choices (correctedMask w S) w)
    (u : PartialSchmidtCoordinates (correctedMask w S) w S) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    freeSourceVector R U V (crossingSlotMask w S) (partialSchmidtSourceVectors A w S E F ξ u) =
      freeSourceVector R U V (crossingSlotMask w S) (partialSlotVector A w ξ) := by
  classical
  intro A R U V
  apply freeSourceVector_congr
  intro i hi
  have hs : i ∉ selectedPartialSlots A w S := by
    intro hs
    have hc : correctedSlotMask w S i = true := by
      simpa only [correctedSlotMask, decide_eq_true_eq] using
        (mem_selectedPartialSlots A w S i).mp hs
    have hf := crossingSlotMask_eq_false_of_corrected w S i hc
    simp [hi] at hf
  simp only [partialSchmidtSourceVectors, dite_eq_right hs]

/-- Every corrected occurrence has an affected endpoint. -/
theorem correctedMask_meets :
    ∀ e ∈ S, correctedMask w S (endpoints w e).1 = true ∨
      correctedMask w S (endpoints w e).2 = true := by
  intro e he
  left
  simp only [correctedMask, decide_eq_true_eq, mem_correctedParties]
  exact ⟨e, he, Or.inl rfl⟩


/-- The exact corrected-column input identity, with one common register
rearrangement before every branch and every original-source coordinate. -/
def HasCorrectedSchmidtInputs (p₀ : Word [] a) : Prop :=
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let ℓ := Layout.mapOwner (affectedOwner A) a
    let C := freeSlotLayout R U V (correctedSlotMask w S)
    let T := freeSlotLayout R U V (crossingSlotMask w S)
    let e := partialSchmidtCoordinateEquiv A w S (correctedMask_meets w S)
    let I := CorrectedSchmidtCoordinates w S
    let X : HSpace := Mem (C ++ T)
    let Y : HSpace := Mem (Layout.mapOwner (affectedOwner A) b)
    let evaluate : Word (C ++ (T ++ ℓ))
        (freeSlotLayout R U V (correctedFreeSlots w S) ++ ℓ) → Choices A w → X → Y :=
      fun u ξ z ↦ (correctedPreparedWord w S p₀ u ξ).eval z
    let input : Choices A w → I → X := fun ξ i ↦
      (appendIso C T).symm
        (freeSourceVector R U V (correctedSlotMask w S)
            (partialSchmidtSourceVectors A w S E F ξ (e.symm i)) ⊗ₜ[ℂ]
          freeSourceVector R U V (crossingSlotMask w S) (partialSlotVector A w ξ))
    let output : Choices A w → I → Y := fun ξ i ↦
      Layout.mapOwnerIso (affectedOwner A) b
        (partialSchmidtOutput A w S E F ξ (e.symm i) (p₀.eval 1))
    ∃ u : Word (C ++ (T ++ ℓ)) (freeSlotLayout R U V (correctedFreeSlots w S) ++ ℓ),
      u.IsAllowed ∧ u.sources = [] ∧ ∀ (ξ : Choices A w) (i : I),
        output ξ i = evaluate u ξ (input ξ i)

/-- The corrected-column input identity follows from the actual uniform source
preparation. No normalization or isometry assumption on the columns is needed. -/
theorem exists_correctedSchmidtInput_identity (p₀ : Word [] a) :
    HasCorrectedSchmidtInputs w S E F p₀ := by
  unfold HasCorrectedSchmidtInputs
  intro A R U V ℓ C T e I X Y evaluate input output
  obtain ⟨u, hu, hus, hinput⟩ := exists_correctedInputVector_identity w S p₀
  refine ⟨u, hu, hus, ?_⟩
  intro ξ i
  have hi := hinput ξ (partialSchmidtSourceVectors A w S E F ξ (e.symm i))
  dsimp only at hi
  rw [fill_partialSchmidtSourceVectors w S E F ξ (e.symm i)] at hi
  dsimp only [output, partialSchmidtOutput]
  rw [LinearIsometryEquiv.apply_symm_apply, hi]
  change (correctedPreparedWord w S p₀ u ξ).eval ((appendIso C T).symm
    (freeSourceVector R U V (correctedSlotMask w S)
        (partialSchmidtSourceVectors A w S E F ξ (e.symm i)) ⊗ₜ[ℂ]
      freeSourceVector R U V (crossingSlotMask w S)
        (partialSchmidtSourceVectors A w S E F ξ (e.symm i)))) = _
  rw [crossingVector_partialSchmidtSourceVectors w S E F ξ (e.symm i)]

end TNLean.PEPS.PairEffect.SourceCircuit
