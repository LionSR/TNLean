/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CorrectedInputVectors

/-!
# Uniform corrected-input vector identity

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

/-- The actual corrected and crossing input representation. A single allowed,
source-free permutation is chosen before every branch and every free vector;
the identity retains the original fixed source vectors and the original input
preparation. This is a conclusion to be derived, with no factorization premise. -/
def HasCorrectedInputVectors {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (p₀ : Word [] a) : Prop :=
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
    ∃ u : Word (C ++ (T ++ ℓ)) (freeSlotLayout R U V free ++ ℓ),
      u.IsAllowed ∧ u.sources = [] ∧ ∀ (ξ : Choices A w) (η : ∀ i, U i ⊗[ℂ] V i),
        output ξ η = F u ξ (input η)

/-- The original prepared partial vector equals the absorbed word on its literal
corrected and crossing source-vector blocks. The common rearrangement is derived
from the original source positions and precedes every branch and free vector. -/
theorem exists_correctedInputVector_identity {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (p₀ : Word [] a) :
    HasCorrectedInputVectors w S p₀ := by
  obtain ⟨u, hu, hus, hue⟩ := exists_correctedInputReordering w S
  exact ⟨u, hu, hus, fun ξ η ↦ correctedInputVector_identity_of_reordering w S p₀ u ξ η (hue η)⟩

end TNLean.PEPS.PairEffect.SourceCircuit
