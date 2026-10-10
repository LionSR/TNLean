/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PreparedSourceVectorDensity
import TNLean.PEPS.Approximation.SourceSlotBasis

/-! # Pure-input coordinates of prepared source vectors

The columns of the source-to-output matrix are the prepared output vectors
obtained from elementary source basis vectors and the given pure input. Each
mixed prepared density coefficient is the outer product of its ket and bra
columns. Empty source inventories and zero input vectors are included.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`, lines 137–139,
  279–355 and 409–434.
-/

noncomputable section
open scoped BigOperators TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect
variable {P : Type}

namespace Word
/-- Columns are the actual output vectors obtained from elementary source
basis vectors and the given pure input. Source: polynomial-PEPS,
`04-compression.tex`, lines 137–139 and 409–434. -/
def pureSourceMatrix {m : Type} [Fintype m] (R : SourceInventory P)
    (U V : Fin R.length → HSpace) {A B : Fin R.length → Type}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (ℓ : Layout P) {ℓ' : Layout P}
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bOut : OrthonormalBasis m ℂ (Mem ℓ')) (ψ : Mem ℓ) :
    Matrix m (∀ i, A i × B i) ℂ := fun r x =>
      bOut.repr (v.eval ((appendIso (SourceInventory.slotLayout R U V) ℓ).symm
        (SourceInventory.slotBasis R U V bU bV x ⊗ₜ[ℂ] ψ))) r

/-- Each actual prepared density coefficient on a pure input is the outer
product of the corresponding literal source-to-output columns.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 409–434. -/
theorem preparedDensityCoefficient_pure_eq_vecMulVec
    {m n : Type} [Fintype m] [Fintype n] (R : SourceInventory P)
    (U V : Fin R.length → HSpace) {A B : Fin R.length → Type}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (ℓ : Layout P) {ℓ' : Layout P}
    (v v' : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ψ : Mem ℓ) (x y : ∀ i, A i × B i) :
    v.preparedDensityCoefficient R U V (fun i => bU i) (fun i => bV i)
      (fun i => bU i) (fun i => bV i) ℓ v' bIn bOut
      (Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j => conj (bIn.repr ψ j))) x y =
      Matrix.vecMulVec (fun r => v.pureSourceMatrix R U V bU bV ℓ bOut ψ r x)
        (fun s => conj (v'.pureSourceMatrix R U V bU bV ℓ bOut ψ s y)) := by
  rw [preparedDensityCoefficient, preparedMatrix_mul_vecMulVec]
  done

end Word
end TNLean.PEPS.PairEffect
