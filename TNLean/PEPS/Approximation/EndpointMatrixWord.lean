/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.BasisMatrixOperator

/-! # Actual endpoint coordinates and their sample average

The literal endpoint operator is expressed in the recorded source-slot bases.
The sample assignments are shared between the two endpoints of each slot.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- The literal endpoint word constructed from specified endpoint matrices in
its actual orthonormal coordinates. No positivity condition is imposed.
Source: polynomial-PEPS 04-compression.tex, lines 279–309 and 565–588. -/
def endpointMatrixWord (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {I J : Fin R.length → Type} [∀ i, Fintype (I i)] [∀ i, Fintype (J i)]
    (bU : ∀ i, OrthonormalBasis (I i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (J i) ℂ (V i))
    (A : ∀ i, Matrix (I i) (I i) ℂ) (B : ∀ i, Matrix (J i) (J i) ℂ) :=
  endpointWord R U V (fun i => basisMatrixOperator (bU i) (A i))
    (fun i => basisMatrixOperator (bV i) (B i))

/-- The actual endpoint matrix word has precisely the product of its specified
matrix entries in the literal source-slot basis.
Source: polynomial-PEPS 04-compression.tex, lines 279–309 and 565–588. -/
theorem slotBasis_repr_endpointMatrixWord (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    {I J : Fin R.length → Type} [∀ i, Fintype (I i)] [∀ i, Fintype (J i)]
    (bU : ∀ i, OrthonormalBasis (I i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (J i) ℂ (V i))
    (A : ∀ i, Matrix (I i) (I i) ℂ) (B : ∀ i, Matrix (J i) (J i) ℂ)
    (x y : ∀ i, I i × J i) :
    (slotBasis R U V bU bV).repr
        ((endpointMatrixWord R U V bU bV A B).eval (slotBasis R U V bU bV y)) x =
      ∏ i, A i (x i).1 (y i).1 * B i (x i).2 (y i).2 := by
  simp only [endpointMatrixWord, slotBasis_repr_endpointWord, basisMatrixOperator_repr]

end TNLean.PEPS.PairEffect.SourceInventory
