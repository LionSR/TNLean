/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PurePreparedContraction
import TNLean.Lattice.Compression.ActualSourceColumnCoordinates
import TNLean.Lattice.Compression.PartialSourceWordEvaluation

/-! # Chronological source columns on a recorded product input

The source coordinates are the Euclidean endpoint bases of the original slots.
A column is obtained by evaluating the actual chronological source word, with
the recorded product input prepared, on an elementary source vector tensored
with scalar one. The prepared density contraction is the product source matrix
between the actual ket and bra column matrices.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`, lines 137–139,
  279–355 and 409–434.
-/
noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.Lattice.PartyCircuit.SourceCircuit
variable {P : Type}

/-- The actual pure-input prepared source contraction is the literal source
product matrix between the two actual chronological column matrices. No
coordinate or factorization identity is supplied as a hypothesis.
Source: polynomial-PEPS, `04-compression.tex`, lines 137–139, 279–355 and 409–434. -/
theorem sourceContraction_preparedDensityCoefficient_pure_eq_mul
    {a b : Layout P} (w : SourceCircuit a b) (ψ : ProductInput a)
    (ξ ζ : Choices (fun _ => true) w) {m n : Type} [Fintype m] [Fintype n]
    (bIn : OrthonormalBasis n ℂ
      (Mem (Layout.mapOwner (affectedOwner (fun _ => true)) a)))
    (bOut : OrthonormalBasis m ℂ
      (Mem (Layout.mapOwner (affectedOwner (fun _ => true)) b)))
    (X : ∀ i : Fin (partialSlots (fun _ => true) w).length,
      Matrix (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1 ×
        Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2)
        (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1 ×
          Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2) ℂ) :
    let R := partialSlots (fun _ => true) w
    let U := fun i : Fin R.length =>
      euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1)
    let V := fun i : Fin R.length =>
      euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2)
    let bU := fun i : Fin R.length =>
      EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1) ℂ
    let bV := fun i : Fin R.length =>
      EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2) ℂ
    let v := Layout.mapOwnerIso (affectedOwner (fun _ => true)) a ψ.vector
    Matrix.sourceContraction (fun x =>
      (partialResidual (fun _ => true) w ξ).preparedDensityCoefficient R U V
        (fun i => bU i) (fun i => bV i) (fun i => bU i) (fun i => bV i)
        (Layout.mapOwner (affectedOwner (fun _ => true)) a)
        (partialResidual (fun _ => true) w ζ) bIn bOut
        (Matrix.vecMulVec (bIn.repr v).ofLp (fun j => conj (bIn.repr v j)))
        (fun i => (x i).1) (fun i => (x i).2)) X =
      w.partialSourceGlobalMatrix ψ ξ bOut * SourceInventory.productSourceMatrix R X *
        (w.partialSourceGlobalMatrix ψ ζ bOut)ᴴ := by
  classical
  let R := partialSlots (fun _ => true) w
  let U := fun i : Fin R.length =>
    euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1)
  let V := fun i : Fin R.length =>
    euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2)
  let bU := fun i : Fin R.length =>
    EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1) ℂ
  let bV := fun i : Fin R.length =>
    EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2) ℂ
  let v := Layout.mapOwnerIso (affectedOwner (fun _ => true)) a ψ.vector
  have hcolumns (η : Choices (fun _ => true) w) :
      (partialResidual (fun _ => true) w η).pureSourceMatrix R U V bU bV
        (Layout.mapOwner (affectedOwner (fun _ => true)) a) bOut v =
      w.partialSourceGlobalMatrix ψ η bOut := by
    ext i x
    exact (congrArg (fun y => bOut.repr y i)
      (eval_partialSourceWord_tmul w ψ η
        (SourceInventory.slotBasis R U V bU bV x))).symm
  dsimp only
  simp_rw [Word.preparedDensityCoefficient_pure_eq_vecMulVec]
  rw [hcolumns ξ, hcolumns ζ]
  exact SourceInventory.sourceContraction_columns_eq_mul R
    (w.partialSourceGlobalMatrix ψ ξ bOut)
    (w.partialSourceGlobalMatrix ψ ζ bOut) X

end TNLean.Lattice.PartyCircuit.SourceCircuit
