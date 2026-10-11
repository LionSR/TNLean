/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionInverse

/-!
# Normalized trace of the inverse fusion comparison

The inverse multiplicity entry is the normalized trace of the actual
left-analysis/right-synthesis contraction. The proof uses the forward
F-move, its public right-inverse identity, and the full left-tree
biorthogonality equation. It does not unfold the choice of an inverse
matrix or use a private fixed-final comparison theorem.

This contraction has the analysis orientation of GLM23's fusion symbol:
left-tree multiplicities are rows and right-tree multiplicities are columns.

## References

* arXiv:1511.08090, `Fmove`, lines 248--251, and the fixed-final argument
  at lines 252--277.
* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `Fsymbolsdef` and
  `coupledpent`; the index correction is recorded in
  `docs/paper-gaps/glm23_multiplicity_l_indices.tex`.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
  (Fus : CompleteZipperFusionFamily Λ p)

/-- A fixed left/right pair of multiplicities in the inverse tree
comparison gives the inverse coefficient times the final bond identity. -/
theorem leftTripleAnalysis_mul_rightTripleSynthesis_eq_smul_one
    (a b c d : Λ) (t : Fus.LeftTripleMultiplicity a b c d)
    (q : Fus.RightTripleMultiplicity a b c d) :
    (Fus.leftTripleAnalysis a b c d).submatrix (fun z ↦ (t, z)) id *
        (Fus.rightTripleSynthesis a b c d).submatrix id (fun z ↦ (q, z)) =
      Fus.inversePrintedFMatrix a b c d t q •
        (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) := by
  classical
  have hS :
      Fus.leftTripleSynthesis a b c d *
          (Fus.inversePrintedFMatrix a b c d ⊗ₖ
            (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) =
        Fus.rightTripleSynthesis a b c d := by
    rw [← Fus.rightTripleSynthesis_mul_printedFMatrix a b c d,
      Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
      Fus.printedFMatrix_mul_inversePrintedFMatrix, Matrix.one_mul,
      Matrix.one_kronecker_one, Matrix.mul_one]
  have hA : Fus.leftTripleAnalysis a b c d * Fus.leftTripleSynthesis a b c d =
      (1 : Matrix
        (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d))
        (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d)) ℂ) := by
    ext x y
    have h := congrArg
      (fun C ↦ C (Fus.leftFinalRow a b c d x) (Fus.leftFinalRow a b c d y))
      (Fus.leftTripleAnalysisFull_mul_synthesis a b c)
    simpa [Matrix.mul_apply, leftTripleAnalysisFull, leftTripleSynthesisFull,
      leftFinalRow, Matrix.one_apply] using h
  have hC :
      Fus.leftTripleAnalysis a b c d * Fus.rightTripleSynthesis a b c d =
        Fus.inversePrintedFMatrix a b c d ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) := by
    rw [← hS, ← Matrix.mul_assoc, hA, Matrix.one_mul]
  ext z w
  change (∑ x, Fus.leftTripleAnalysis a b c d (t, z) x *
      Fus.rightTripleSynthesis a b c d x (q, w)) =
    Fus.inversePrintedFMatrix a b c d t q *
      (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) z w
  have h := congrArg (fun C ↦ C (t, z) (q, w)) hC
  simpa only [Matrix.mul_apply, Matrix.kroneckerMap_apply] using h

/-- The normalized trace recovers an inverse multiplicity entry from the
left-analysis/right-synthesis contraction. Positivity of the final bond
dimension is part of the complete zipper family. -/
theorem inversePrintedFMatrix_eq_inv_dim_mul_trace
    (a b c d : Λ) (t : Fus.LeftTripleMultiplicity a b c d)
    (q : Fus.RightTripleMultiplicity a b c d) :
    Fus.inversePrintedFMatrix a b c d t q = (Fus.bondDim d : ℂ)⁻¹ *
      Matrix.trace ((Fus.leftTripleAnalysis a b c d).submatrix (fun z ↦ (t, z)) id *
        (Fus.rightTripleSynthesis a b c d).submatrix id (fun z ↦ (q, z))) := by
  rw [Fus.leftTripleAnalysis_mul_rightTripleSynthesis_eq_smul_one,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    mul_comm (Fus.inversePrintedFMatrix a b c d t q), ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Fus.bondDim_pos d).ne'), one_mul]

end MPOTensor.CompleteZipperFusionFamily
