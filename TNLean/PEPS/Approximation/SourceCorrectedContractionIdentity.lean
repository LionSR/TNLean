/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCorrectedSlots
import TNLean.PEPS.Approximation.SelectedSourceContraction

/-!
# Source contractions of actual corrected circuit terms

A corrected term is indexed by the original source occurrences, independently
of the affected set. For any affected set meeting every selected occurrence,
its partial expansion gives the same term as a weighted sum of contractions of
the actual canonical residual words. The selected matrices retain the local
ket and bra gate labels; all unselected sources remain their exact vectors.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-corrections-sourcecorrectedcontractionidentity-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.correctedSourceTerm_eq_sourceContraction

-/

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

/-- The original corrected circuit term is the partial-branch sum of actual
prepared source contractions. Source occurrences, local gate labels, branch
coefficients, and independent ket and bra endpoint indices are all preserved.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–434. -/
theorem correctedSourceTerm_eq_sourceContraction {P m n : Type}
    [Fintype m] [Fintype n] (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) :
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let bU := fun i : Fin R.length ↦
      EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).1) ℂ
    let bV := fun i : Fin R.length ↦
      EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).2) ℂ
    correctedSourceTerm w S E bIn bOut ρ =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        Matrix.sourceContraction
          (fun z ↦ (partialResidual A w ξ).preparedDensityCoefficient R U V
            (fun i ↦ bU i) (fun i ↦ bV i) (fun i ↦ bU i) (fun i ↦ bV i)
            (Layout.mapOwner (affectedOwner A) a) (partialResidual A w ζ)
            (bIn.map (Layout.mapOwnerIso (affectedOwner A) a))
            (bOut.map (Layout.mapOwnerIso (affectedOwner A) b)) ρ
            (fun i ↦ (z i).1) (fun i ↦ (z i).2))
          (fun i ↦ if i ∈ selectedPartialSlots A w S then
            E (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) (partialSlotChoice A w ζ i)
          else Matrix.vecMulVec (((bU i).tensorProduct (bV i)).repr (partialSlotVector A w ξ i))
            (fun j ↦ conj (((bU i).tensorProduct (bV i)).repr (partialSlotVector A w ζ i) j))) := by
  classical
  dsimp only
  rw [correctedSourceTerm_eq_sum_coordinates A w S hS]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ ?_
  apply congrArg (fun M : Matrix m m ℂ ↦ (coefficient A w ξ * conj (coefficient A w ζ)) • M)
  symm
  rw [Word.sourceContraction_preparedDensityCoefficient_selected]
  apply Fintype.sum_equiv (selectedSourceCoordinateEquiv A w S hS)
  intro u
  apply Fintype.sum_equiv (selectedSourceCoordinateEquiv A w S hS)
  intro v
  rw [partialCoordinateBasisMatrix_reindex, partialCoordinateBasisMatrix_reindex]
  congr 1
  apply Fintype.prod_equiv (selectedPartialSlotEquiv A w S hS)
  intro i
  rw [selectedSourceCoordinateEquiv_apply, selectedSourceCoordinateEquiv_apply]
  rfl

end TNLean.PEPS.PairEffect.SourceCircuit
