/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionPentagon

/-!
# Mixed orientation of the actual fourfold fusion comparison

The proved forward pentagon has the form `C * B * A = E * D`. Cancelling
its first edge on the right gives `E * D * A⁻¹ = C * B`. In the triangular
operator/state embedding, the four remaining forward edges are the actual
L matrices, while the inverse first edge is GLM23's analysis-oriented F.

Both identities below follow from the constructed complete-zipper matrices.
No pentagon equation is a premise. Identifying their typed entries with the
source fusion/action maps is a separate algebraic step.

**Local fix (multiplicity indices):** GLM23's coupled pentagon must use the
F entry with upper `(d,η,χ)` and lower `(f,μ,ν)`; the printed source reverses
both pairs. See `docs/paper-gaps/glm23_multiplicity_l_indices.tex`.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `coupledpent`,
  lines 554--562.
* arXiv:1511.08090, `Fmove` and `pentagoneq`, lines 248--299.
-/

open scoped Matrix Kronecker

namespace MPOTensor.CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
  (Fus : CompleteZipperFusionFamily Λ p)

/-- The first lifted forward comparison followed by its inverse is the
identity on the left-inner fourfold multiplicity space. This is the inverse
direction needed to turn the ordinary pentagon into GLM23's mixed one. -/
theorem leftAssocToLeftInner_mul_leftInnerToLeftAssocInverse (a b c d e : Λ) :
    Fus.leftAssocToLeftInnerPrintedFMatrix a b c d e *
      Fus.leftInnerToLeftAssocInversePrintedFMatrix a b c d e = 1 := by
  unfold leftAssocToLeftInnerPrintedFMatrix leftInnerToLeftAssocInversePrintedFMatrix
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
  simp only [← Matrix.mul_kronecker_mul,
    Fus.printedFMatrix_mul_inversePrintedFMatrix, Matrix.one_mul,
    Matrix.one_kronecker_one]
  change (Matrix.blockDiagonal'
    (1 : (g : Λ) → Matrix
      (Fus.RightTripleMultiplicity a b c g × Fin (Fus.fusionMultiplicity g d e))
      (Fus.RightTripleMultiplicity a b c g × Fin (Fus.fusionMultiplicity g d e)) ℂ)).submatrix
        _ _ = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

/-- The actual fourfold coordinate changes satisfy the mixed-orientation
pentagon `E D A⁻¹ = C B`. This is obtained from the proved ordinary pentagon,
not by adding a coherence field to the fusion data. -/
theorem twoEdgePrintedFMatrix_mul_leftInnerToLeftAssocInverse (a b c d e : Λ) :
    Fus.twoEdgePrintedFMatrix a b c d e *
        Fus.leftInnerToLeftAssocInversePrintedFMatrix a b c d e =
      Fus.middleToRightAssocPrintedFMatrix a b c d e *
        Fus.leftInnerToMiddlePrintedFMatrix a b c d e := by
  rw [← Fus.threeEdgePrintedFMatrix_eq_twoEdgePrintedFMatrix,
    threeEdgePrintedFMatrix, Matrix.mul_assoc,
    Fus.leftAssocToLeftInner_mul_leftInnerToLeftAssocInverse, Matrix.mul_one]

end MPOTensor.CompleteZipperFusionFamily
