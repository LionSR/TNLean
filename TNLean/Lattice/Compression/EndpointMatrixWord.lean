/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.BasisMatrixOperator
import TNLean.Lattice.Compression.EndpointOperatorCoordinates

/-! # The endpoint word of specified endpoint matrices

The literal endpoint word is built from one matrix at each endpoint of every
source slot, read through the recorded orthonormal bases, and its matrix in
the slot basis is the product of the specified entries. No sampling or
averaging occurs here.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–309 and 565–588.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 253–267, 279–355 and 565–588.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit.SourceInventory
open TNLean.PEPS.PairEffect
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

end TNLean.Lattice.PartyCircuit.SourceInventory
