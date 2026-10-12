/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointWordEvaluation
import TNLean.PEPS.Approximation.SourceSlotCoordinates

/-! # Actual endpoint coordinates and their sample average

The literal endpoint operator is expressed in the recorded source-slot bases.
The sample assignments are shared between the two endpoints of each slot.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 253–267, 279–355 and 565–588.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- The matrix of the literal endpoint word in the actual slot basis is the
product of the two endpoint matrix entries at each source occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 279–309 and 565–588. -/
theorem slotBasis_repr_endpointWord (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    {I J : Fin R.length → Type} [∀ i, Fintype (I i)] [∀ i, Fintype (J i)]
    (bU : ∀ i, OrthonormalBasis (I i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (J i) ℂ (V i))
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i)
    (x y : ∀ i, I i × J i) :
    (slotBasis R U V bU bV).repr
        ((endpointWord R U V A B).eval (slotBasis R U V bU bV y)) x =
      ∏ i, (bU i).repr (A i (bU i (y i).1)) (x i).1 *
        (bV i).repr (B i (bV i (y i).2)) (x i).2 := by
  rw [slotBasis_apply, eval_endpointWord_slotVector_tmul, slotBasis_repr_slotVector]
  simp only [OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.tensorProduct_apply', TensorProduct.inner_tmul]

end TNLean.PEPS.PairEffect.SourceInventory
