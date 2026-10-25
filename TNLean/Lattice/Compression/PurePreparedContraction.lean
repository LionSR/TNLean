/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PureSourceMatrix
import TNLean.Lattice.Compression.SourceColumnContraction

/-!
# Contraction of pure prepared source coefficients

The source matrices are arbitrary complex matrices. Their product is inserted
between the actual source-to-output matrices of the ket and bra words. The
input vector need not be normalized, and the two words may differ.

Source: polynomial-PEPS manuscript, proof of Theorem 5.2,
`04-compression.tex`, lines 279–355 and 409–434.
-/

noncomputable section
open scoped BigOperators Matrix ComplexConjugate
namespace TNLean.Lattice.PartyCircuit.Word

/-- The contraction on a pure input is the product source matrix between the
literal ket and bra source-to-output matrices.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 409–434. -/
theorem sourceContraction_preparedDensityCoefficient_pure_eq_mul
    {P m n : Type} [Fintype m] [Fintype n] (R : SourceInventory P)
    (U V : Fin R.length → HSpace) {A B : Fin R.length → Type}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (ℓ : Layout P) {ℓ' : Layout P}
    (v v' : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ψ : Mem ℓ) (X : ∀ i, Matrix (A i × B i) (A i × B i) ℂ) :
    Matrix.sourceContraction
      (fun x ↦ v.preparedDensityCoefficient R U V (fun i ↦ bU i) (fun i ↦ bV i)
        (fun i ↦ bU i) (fun i ↦ bV i) ℓ v' bIn bOut
        (Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr ψ j)))
        (fun i ↦ (x i).1) (fun i ↦ (x i).2)) X =
      v.pureSourceMatrix R U V bU bV ℓ bOut ψ *
        SourceInventory.productSourceMatrix R X *
        (v'.pureSourceMatrix R U V bU bV ℓ bOut ψ)ᴴ := by
  exact (congrArg (fun coeff ↦ Matrix.sourceContraction coeff X)
    (funext fun x ↦ preparedDensityCoefficient_pure_eq_vecMulVec
      R U V bU bV ℓ v v' bIn bOut ψ
      (fun i ↦ (x i).1) (fun i ↦ (x i).2))).trans
    (SourceInventory.sourceContraction_columns_eq_mul R
      (v.pureSourceMatrix R U V bU bV ℓ bOut ψ)
      (v'.pureSourceMatrix R U V bU bV ℓ bOut ψ) X)

end TNLean.Lattice.PartyCircuit.Word
