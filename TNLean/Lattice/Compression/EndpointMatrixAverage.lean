/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.EndpointMatrixWord

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
open scoped Kronecker
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- Averaging the actual endpoint words is the product of the original slot
averages in the fixed source coordinates. The identity includes empty source
inventories and zero samples and imposes no positivity condition.
Source: polynomial-PEPS 04-compression.tex, lines 279–309 and 565–588. -/
theorem endpointMatrixAverage_eq_product (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    {I J : Fin R.length → Type} [∀ i, Fintype (I i)] [∀ i, Fintype (J i)]
    (bU : ∀ i, OrthonormalBasis (I i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (J i) ℂ (V i)) (k : ℕ)
    (A : ∀ i, Fin k → Matrix (I i) (I i) ℂ)
    (B : ∀ i, Fin k → Matrix (J i) (J i) ℂ)
    (x y : ∀ i, I i × J i) :
    ∏ i, ((k : ℂ)⁻¹ • ∑ j : Fin k, A i j ⊗ₖ B i j) (x i) (y i) =
      ((k : ℂ)⁻¹ ^ R.length) *
        ∑ j : Fin R.length → Fin k,
          (slotBasis R U V bU bV).repr
            ((endpointMatrixWord R U V bU bV (fun i => A i (j i))
              (fun i => B i (j i))).eval (slotBasis R U V bU bV y)) x := by
  classical
  simp only [slotBasis_repr_endpointMatrixWord, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  change (∏ i, (k : ℂ)⁻¹ * ∑ j : Fin k,
    A i j (x i).1 (y i).1 * B i j (x i).2 (y i).2) = _
  rw [Finset.prod_mul_distrib, Fintype.prod_sum]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end TNLean.PEPS.PairEffect.SourceInventory
