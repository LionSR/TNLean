/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCorrectedContraction

/-!
# Selected original positions in the partial source slots

The canonical occurrence enumeration identifies selected original source
positions with precisely their retained finite slots.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-corrections-sourcecorrectedslots-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.selectedPartialSlots

Provenance-ID: 8769-source-corrections-sourcecorrectedslots-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.mem_selectedPartialSlots

Provenance-ID: 8769-source-corrections-sourcecorrectedslots-03
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.selectedPartialSlotEquiv

Provenance-ID: 8769-source-corrections-sourcecorrectedslots-04
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.selectedSourceCoordinateEquiv

Provenance-ID: 8769-source-corrections-sourcecorrectedslots-05
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.selectedSourceCoordinateEquiv_apply

Provenance-ID: 8769-source-corrections-sourcecorrectedslots-06
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.partialCoordinateBasisMatrix_reindex

-/

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The partial slots belonging to the selected original positions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def selectedPartialSlots (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (S : Finset (sourceLocations w)) :
    Finset (Fin (partialSlots A w).length) := by
  classical
  exact Finset.univ.filter fun i ↦ (partialSlotEquiv A w i).1 ∈ S

/-- Membership retains the original occurrence, independently of branch choices.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem mem_selectedPartialSlots (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (i : Fin (partialSlots A w).length) :
    i ∈ selectedPartialSlots A w S ↔ (partialSlotEquiv A w i).1 ∈ S := by
  classical
  simp [selectedPartialSlots]

/-- Every selected source meeting the affected mask corresponds to exactly one partial slot.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def selectedPartialSlotEquiv (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true) :
    selectedPartialSlots A w S ≃ S where
  toFun i := ⟨(partialSlotEquiv A w i.1).1, (mem_selectedPartialSlots A w S i.1).mp i.2⟩
  invFun e := ⟨(partialSlotEquiv A w).symm ⟨e.1, hS e.1 e.2⟩, by
    rw [mem_selectedPartialSlots, Equiv.apply_symm_apply]
    exact e.2⟩
  left_inv i := by
    apply Subtype.ext
    exact (partialSlotEquiv A w).symm_apply_apply i.1
  right_inv e := by
    have h := congrArg Subtype.val
      ((partialSlotEquiv A w).apply_symm_apply ⟨e.1, hS e.1 e.2⟩)
    exact Subtype.ext h

/-- Reindex selected endpoint assignments by their original source occurrences.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def selectedSourceCoordinateEquiv (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true) :
    (∀ i : selectedPartialSlots A w S,
      Fin (sourceDims w (partialSlotEquiv A w i.1).1).1 ×
        Fin (sourceDims w (partialSlotEquiv A w i.1).1).2) ≃
      SelectedSourceCoordinates w S :=
  Equiv.piCongrLeft (fun e : S ↦ Fin (sourceDims w e.1).1 × Fin (sourceDims w e.1).2)
    (selectedPartialSlotEquiv A w S hS)

/-- At the corresponding original occurrence, reindexing reads the same coordinates.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem selectedSourceCoordinateEquiv_apply (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (u : ∀ i : selectedPartialSlots A w S,
      Fin (sourceDims w (partialSlotEquiv A w i.1).1).1 ×
        Fin (sourceDims w (partialSlotEquiv A w i.1).1).2)
    (i : selectedPartialSlots A w S) :
    selectedSourceCoordinateEquiv A w S hS u (selectedPartialSlotEquiv A w S hS i) = u i :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

open Classical in
/-- The original-occurrence basis substitution agrees with the finite-slot
preparation through the same canonical partial residual.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem partialCoordinateBasisMatrix_reindex {m n : Type} [Fintype m] [Fintype n]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (u : ∀ i : selectedPartialSlots A w S,
      Fin (sourceDims w (partialSlotEquiv A w i.1).1).1 ×
        Fin (sourceDims w (partialSlotEquiv A w i.1).1).2)
    (ξ : Choices A w) (bIn : OrthonormalBasis n ℂ (Mem a))
    (bOut : OrthonormalBasis m ℂ (Mem b)) :
    partialCoordinateBasisMatrix A w S (selectedSourceCoordinateEquiv A w S hS u) ξ bIn bOut =
      (partialResidual A w ξ).preparedMatrix (partialSlots A w)
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
        (fun i ↦ if h : i ∈ selectedPartialSlots A w S then
          EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).1) ℂ
              (u ⟨i, h⟩).1 ⊗ₜ[ℂ]
            EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).2) ℂ
              (u ⟨i, h⟩).2
          else partialSlotVector A w ξ i)
        (Layout.mapOwner (affectedOwner A) a)
        (bIn.map (Layout.mapOwnerIso (affectedOwner A) a))
        (bOut.map (Layout.mapOwnerIso (affectedOwner A) b)) := by
  rw [partialCoordinateBasisMatrix_eq_preparedMatrix A w S hS]
  apply congrArg (fun η ↦ (partialResidual A w ξ).preparedMatrix (partialSlots A w)
    (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
    (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)) η
    (Layout.mapOwner (affectedOwner A) a)
    (bIn.map (Layout.mapOwnerIso (affectedOwner A) a))
    (bOut.map (Layout.mapOwnerIso (affectedOwner A) b)))
  funext i
  by_cases hi : i ∈ selectedPartialSlots A w S
  · have he := (mem_selectedPartialSlots A w S i).mp hi
    have hc := selectedSourceCoordinateEquiv_apply A w S hS u ⟨i, hi⟩
    simp only [selectedSourceVectors, ite_eq_left he, coordinateBasisVectors,
      dite_eq_left he, dite_eq_left hi]
    exact congrArg (fun z : Fin (sourceDims w (partialSlotEquiv A w i).1).1 ×
        Fin (sourceDims w (partialSlotEquiv A w i).1).2 ↦
      EuclideanSpace.basisFun _ ℂ z.1 ⊗ₜ[ℂ] EuclideanSpace.basisFun _ ℂ z.2) hc
  · have he := mt (mem_selectedPartialSlots A w S i).mpr hi
    simp only [selectedSourceVectors, ite_eq_right he, dite_eq_right hi, partialSlotVector]

end TNLean.PEPS.PairEffect.SourceCircuit
