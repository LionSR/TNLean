/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePreparationVectors
import TNLean.PEPS.Approximation.CorrectedInputReordering

/-!
# Corrected input vectors and their actual prepared words

The corrected and crossing vectors occupy their literal original-source
registers. A given source reordering identifies their prepared output with the
original partial circuit vector.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation SourceInventory
variable {P : Type}

/-- Absorb the original input preparation before the corrected and crossing
registers are rearranged. The two free source blocks remain literal layouts. -/
def correctedInputPreparation {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (p₀ : Word [] a) :=
  let A := correctedMask w S
  let R := partialSlots A w
  let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
  let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
  let ℓ := Layout.mapOwner (affectedOwner A) a
  let C := freeSlotLayout R U V (correctedSlotMask w S)
  let T := freeSlotLayout R U V (crossingSlotMask w S)
  (Word.frameList (C ++ T) (p₀.mapOwner (affectedOwner A))).castLayouts
    (List.append_nil _) (List.append_assoc C T ℓ)

/-- The actual residual word after absorbing the initial preparation and
rearranging the two free source blocks. Fixed sources retain their original vectors. -/
def correctedPreparedWord {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (p₀ : Word [] a) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let ℓ := Layout.mapOwner (affectedOwner A) a
    let C := freeSlotLayout R U V (correctedSlotMask w S)
    let T := freeSlotLayout R U V (crossingSlotMask w S)
    Word (C ++ (T ++ ℓ)) (freeSlotLayout R U V (correctedFreeSlots w S) ++ ℓ) →
      Choices A w → Word (C ++ T) (Layout.mapOwner (affectedOwner A) b) := by
  intro A R U V ℓ C T u ξ
  exact SourceInventory.preparedReorderedWord R U V
    (correctedSlotMask w S) (crossingSlotMask w S) (correctedFreeSlots w S)
    (fun i _ ↦ partialSlotVector A w ξ i) (p₀.mapOwner (affectedOwner A))
    (partialResidual A w ξ) u

/-- The literal corrected source block followed by the literal crossing block,
with the terminal scalar supplied by the preparation convention. -/
def correctedInputVector {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    (∀ i, U i ⊗[ℂ] V i) → Mem
      (freeSlotLayout R U V (correctedSlotMask w S) ++
        freeSlotLayout R U V (crossingSlotMask w S)) := by
  intro A R U V η
  exact SourceInventory.sourceVectorPair R U V (correctedSlotMask w S)
    (crossingSlotMask w S) η

set_option Elab.async false in
set_option maxHeartbeats 400000 in
-- Identifying the dependent source memories requires additional elaboration steps.
/-- Once the actual common permutation is fixed, preparation identifies its
absorbed residual output with the original partial circuit vector. -/
theorem correctedInputVector_identity_of_reordering {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (p₀ : Word [] a) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let ℓ := Layout.mapOwner (affectedOwner A) a
    let C := freeSlotLayout R U V (correctedSlotMask w S)
    let T := freeSlotLayout R U V (crossingSlotMask w S)
    let free := correctedFreeSlots w S
    let v : Choices A w → Word (slotLayout R U V ++ ℓ)
        (Layout.mapOwner (affectedOwner A) b) := fun ξ ↦ partialResidual A w ξ
    let fixed : ∀ _ξ : Choices A w, ∀ i : Fin R.length, free i = false → U i ⊗[ℂ] V i :=
      fun ξ i _ ↦ partialSlotVector A w ξ i
    let X : HSpace := Mem (C ++ T)
    let Y : HSpace := Mem (Layout.mapOwner (affectedOwner A) b)
    let F : Word (C ++ (T ++ ℓ)) (freeSlotLayout R U V free ++ ℓ) →
        Choices A w → X → Y := fun u ξ z ↦ (correctedPreparedWord w S p₀ u ξ).eval z
    let input : (∀ i, U i ⊗[ℂ] V i) → X := correctedInputVector w S
    let output : Choices A w → (∀ i, U i ⊗[ℂ] V i) → Y := fun ξ η ↦
      (v ξ).eval ((prepareSlots R U V (fillSourceVectors R U V free (fixed ξ) η) ℓ).eval
        (Layout.mapOwnerIso (affectedOwner A) a (p₀.eval 1)))
    ∀ (u : Word (C ++ (T ++ ℓ)) (freeSlotLayout R U V free ++ ℓ))
      (ξ : Choices A w) (η : ∀ i, U i ⊗[ℂ] V i),
      u.eval ∘L (prepareFreeSlots R U V (correctedSlotMask w S) η (T ++ ℓ)).eval ∘L
        (prepareFreeSlots R U V (crossingSlotMask w S) η ℓ).eval =
          (prepareFreeSlots R U V free η ℓ).eval →
        output ξ η = F u ξ (input η) := by
  intro A R U V ℓ C T free v fixed X Y F input output u ξ η hue
  let p : Word [] ℓ := p₀.mapOwner (affectedOwner A)
  have hp : p.eval 1 = Layout.mapOwnerIso (affectedOwner A) a (p₀.eval 1) :=
    Word.eval_mapOwner (affectedOwner A) p₀ 1
  have he := SourceInventory.eval_reordered_prepared_vector R U V
    (correctedSlotMask w S) (crossingSlotMask w S) free (fixed ξ) η p (v ξ) u hue
    (Layout.mapOwnerIso (affectedOwner A) a (p₀.eval 1)) hp
  exact he


end TNLean.PEPS.PairEffect.SourceCircuit
