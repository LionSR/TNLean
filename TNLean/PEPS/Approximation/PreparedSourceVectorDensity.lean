/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGateDensity

/-!
# Prepared source densities on actual pure inputs

Applying the prepared ket and bra matrices to a rank-one input gives the
rank-one matrix of their actual output vectors. The input vector may in
particular be prepared by the product-input word. This identity does not
require normalization or contractivity.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139 and 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-preparedsourcevectordensity-01
Downstream declaration:
TNLean.PEPS.PairEffect.Word.preparedMatrix_mulVec_repr

Provenance-ID: 8769-physical-preparedsourcevectordensity-02
Downstream declaration:
TNLean.PEPS.PairEffect.Word.preparedMatrix_mul_vecMulVec

Provenance-ID: 8769-physical-preparedsourcevectordensity-03
Downstream declaration:
TNLean.PEPS.PairEffect.Word.preparedMatrix_mul_vecMulVec_preparedInput

-/


noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.Word

variable {P m n : Type} [Fintype m] [Fintype n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η ζ : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) {ℓ' : Layout P}
    (v w : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))

/-- Prepared source matrices act on the coordinates of the actual input vector. -/
theorem preparedMatrix_mulVec_repr (ψ : Mem ℓ) :
    v.preparedMatrix R U V η ℓ bIn bOut *ᵥ (bIn.repr ψ).ofLp =
      (bOut.repr (v.eval ((SourceInventory.prepareSlots R U V η ℓ).eval ψ))).ofLp := by
  classical
  exact LinearMap.toMatrix_mulVec_repr bIn.toBasis bOut.toBasis
    (v.eval.comp (SourceInventory.prepareSlots R U V η ℓ).eval).toLinearMap ψ

/-- A mixed pure input produces precisely the mixed pair of actual prepared
output vectors, with the bra conjugated in the output coordinates. -/
theorem preparedMatrix_mul_vecMulVec (ψ φ : Mem ℓ) :
    v.preparedMatrix R U V η ℓ bIn bOut *
        Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr φ j)) *
          (w.preparedMatrix R U V ζ ℓ bIn bOut)ᴴ =
      Matrix.vecMulVec
        (bOut.repr (v.eval ((SourceInventory.prepareSlots R U V η ℓ).eval ψ))).ofLp
        (fun j ↦ conj (bOut.repr
          (w.eval ((SourceInventory.prepareSlots R U V ζ ℓ).eval φ)) j)) := by
  classical
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    preparedMatrix_mulVec_repr]
  change Matrix.vecMulVec _ (star (bIn.repr φ).ofLp ᵥ*
    (w.preparedMatrix R U V ζ ℓ bIn bOut)ᴴ) = _
  rw [← Matrix.star_mulVec, preparedMatrix_mulVec_repr]
  rfl

/-- Absorbing an actual input-preparation word gives the same prepared vectors
as applying its output vector directly. -/
theorem preparedMatrix_mul_vecMulVec_preparedInput (p : Word [] ℓ) :
    v.preparedMatrix R U V η ℓ bIn bOut *
        Matrix.vecMulVec (bIn.repr (p.eval 1)).ofLp
          (fun j ↦ conj (bIn.repr (p.eval 1) j)) *
          (w.preparedMatrix R U V ζ ℓ bIn bOut)ᴴ =
      Matrix.vecMulVec
        (bOut.repr ((Word.comp p
          (.comp (SourceInventory.prepareSlots R U V η ℓ) v)).eval 1)).ofLp
        (fun j ↦ conj (bOut.repr ((Word.comp p
          (.comp (SourceInventory.prepareSlots R U V ζ ℓ) w)).eval 1) j)) := by
  exact preparedMatrix_mul_vecMulVec R U V η ζ ℓ v w bIn bOut (p.eval 1) (p.eval 1)

end TNLean.PEPS.PairEffect.Word
