/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusion

/-!
# Normalized trace of the constructed fusion comparison

The fixed-final comparison is scalar on the final virtual bond. Its
multiplicity entry can therefore be recovered by the normalized trace of
the actual right analysis followed by left synthesis. This gives a direct
coordinate bridge to the source-oriented action L matrix without choosing
a new basis or a new normalization.

Source: arXiv:1511.08090, `Fmove`, and Garre-Rubio--Lootens--Molnár,
arXiv:2203.12563v3, `1Fsymbol` and `eq:F_symbol2`.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
  (Fus : CompleteZipperFusionFamily Λ p)

/-- A fixed pair of multiplicity indices in the actual triple-tree
comparison leaves the printed coefficient times the identity final bond. -/
theorem rightTripleAnalysis_mul_leftTripleSynthesis_eq_smul_one
    (a b c d : Λ) (q : Fus.RightTripleMultiplicity a b c d)
    (t : Fus.LeftTripleMultiplicity a b c d) :
    (Fus.rightTripleAnalysis a b c d).submatrix (fun z ↦ (q, z)) id *
        (Fus.leftTripleSynthesis a b c d).submatrix id (fun z ↦ (t, z)) =
      Fus.printedFMatrix a b c d q t •
        (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) := by
  ext z w
  change _ = Fus.printedFMatrix a b c d q t *
    (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) z w
  have h := congrArg (fun C ↦ C (q, z) (t, w))
    (Fus.printedFMatrixAmplified_eq_kronecker_one a b c d)
  simpa only [printedFMatrixAmplified, fullPrintedFMatrix, Matrix.submatrix_apply,
    rightFinalRow, leftFinalRow, Matrix.mul_apply, rightTripleAnalysisFull,
    leftTripleSynthesisFull, Matrix.kroneckerMap_apply, id_eq] using h

/-- The normalized trace reads a printed multiplicity entry from the
actual right-analysis/left-synthesis contraction. The positive bond
dimension is a field of the complete zipper family. -/
theorem printedFMatrix_eq_inv_dim_mul_trace
    (a b c d : Λ) (q : Fus.RightTripleMultiplicity a b c d)
    (t : Fus.LeftTripleMultiplicity a b c d) :
    Fus.printedFMatrix a b c d q t = (Fus.bondDim d : ℂ)⁻¹ *
      Matrix.trace ((Fus.rightTripleAnalysis a b c d).submatrix (fun z ↦ (q, z)) id *
        (Fus.leftTripleSynthesis a b c d).submatrix id (fun z ↦ (t, z))) := by
  rw [Fus.rightTripleAnalysis_mul_leftTripleSynthesis_eq_smul_one,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    mul_comm (Fus.printedFMatrix a b c d q t), ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Fus.bondDim_pos d).ne'), one_mul]

end MPOTensor.CompleteZipperFusionFamily
