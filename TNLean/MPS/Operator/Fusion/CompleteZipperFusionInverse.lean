/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Fusion.CompleteZipperFusion

/-!
# Inverse of the printed F-move

The full comparison matrices for the two triple-fusion trees are inverse.
Their fixed-final corners therefore give mutually inverse multiplicity
matrices after the common final bond factor is removed.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 248--251 and 269--277.

## Normalized trace of the inverse fusion comparison

The inverse multiplicity entry is the normalized trace of the actual
left-analysis/right-synthesis contraction. The proof uses the forward
F-move, its public right-inverse identity, and the full left-tree
biorthogonality equation. It does not unfold the choice of an inverse
matrix or use a private fixed-final comparison theorem.

This contraction has the analysis orientation of GLM23's fusion symbol:
left-tree multiplicities are rows and right-tree multiplicities are columns.

### References

* arXiv:1511.08090, `Fmove`, lines 248--251, and the fixed-final argument
  at lines 252--277.
* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `Fsymbolsdef` and
  `coupledpent`; the index correction is recorded in
  `docs/paper-gaps/glm23_multiplicity_l_indices.tex`.
-/

section

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor.CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fus : CompleteZipperFusionFamily Λ p)

private theorem leftLetter_mul_fullInverse (a b c : Λ) (i k : Fin p) :
    Fus.leftTripleDirectSumLetter a b c i k * Fus.fullInversePrintedFMatrix a b c =
      Fus.fullInversePrintedFMatrix a b c * Fus.rightTripleDirectSumLetter a b c i k := by
  calc
    _ = (Fus.fullInversePrintedFMatrix a b c * Fus.fullPrintedFMatrix a b c) *
        (Fus.leftTripleDirectSumLetter a b c i k *
          Fus.fullInversePrintedFMatrix a b c) := by
      rw [Fus.fullInversePrintedFMatrix_mul_fullPrintedFMatrix, Matrix.one_mul]
    _ = Fus.fullInversePrintedFMatrix a b c *
        ((Fus.fullPrintedFMatrix a b c * Fus.leftTripleDirectSumLetter a b c i k) *
          Fus.fullInversePrintedFMatrix a b c) := by simp only [Matrix.mul_assoc]
    _ = Fus.fullInversePrintedFMatrix a b c *
        ((Fus.rightTripleDirectSumLetter a b c i k * Fus.fullPrintedFMatrix a b c) *
          Fus.fullInversePrintedFMatrix a b c) := by
      rw [Fus.rightTripleDirectSumLetter_mul_fullPrintedFMatrix]
    _ = (Fus.fullInversePrintedFMatrix a b c *
        Fus.rightTripleDirectSumLetter a b c i k) *
          (Fus.fullPrintedFMatrix a b c * Fus.fullInversePrintedFMatrix a b c) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [Fus.fullPrintedFMatrix_mul_fullInversePrintedFMatrix, Matrix.mul_one]

private theorem exists_inverseCorner_eq_kronecker_one (a b c d : Λ) :
    ∃ G : Matrix (Fus.LeftTripleMultiplicity a b c d)
        (Fus.RightTripleMultiplicity a b c d) ℂ,
      (Fus.fullInversePrintedFMatrix a b c).submatrix
          (Fus.leftFinalRow a b c d) (Fus.rightFinalRow a b c d) =
        G ⊗ₖ (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) := by
  apply Matrix.exists_eq_kronecker_one_of_intertwines_span_eq_top
    (Fus.tensor d)
    ((Fus.fullInversePrintedFMatrix a b c).submatrix
      (Fus.leftFinalRow a b c d) (Fus.rightFinalRow a b c d))
    (Fus.tensor_injective d).span_eq_top
  intro ij
  obtain ⟨i, k⟩ := ij
  have hFull := Fus.leftLetter_mul_fullInverse a b c i k
  funext ⟨mL, x⟩ ⟨mR, y⟩
  have hEntry := congrArg
    (fun M => M (Fus.leftFinalRow a b c d ⟨mL, x⟩)
      (Fus.rightFinalRow a b c d ⟨mR, y⟩)) hFull
  have hLeft :
      (Fus.leftTripleDirectSumLetter a b c i k *
        Fus.fullInversePrintedFMatrix a b c)
          (Fus.leftFinalRow a b c d ⟨mL, x⟩)
          (Fus.rightFinalRow a b c d ⟨mR, y⟩) =
        ∑ z, Fus.tensor d (i, k) x z * Fus.fullInversePrintedFMatrix a b c
          (Fus.leftFinalRow a b c d ⟨mL, z⟩)
          (Fus.rightFinalRow a b c d ⟨mR, y⟩) := by
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single d
      (fun q _ hq => Finset.sum_eq_zero fun z _ => by
        rw [leftTripleDirectSumLetter, leftFinalRow,
          Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hq), zero_mul])
      (fun h => absurd (Finset.mem_univ d) h)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single mL
      (fun q _ hq => Finset.sum_eq_zero fun z _ => by
        rw [leftTripleDirectSumLetter, leftFinalRow,
          Matrix.blockDiagonal'_apply_eq]
        simp only [kroneckerMap_apply, Matrix.one_apply,
          ite_eq_right (Ne.symm hq), zero_mul])
      (fun h => absurd (Finset.mem_univ mL) h)]
    simp [leftTripleDirectSumLetter, leftFinalRow, rightFinalRow,
      Matrix.blockDiagonal'_apply_eq]
  have hRight :
      (Fus.fullInversePrintedFMatrix a b c *
        Fus.rightTripleDirectSumLetter a b c i k)
          (Fus.leftFinalRow a b c d ⟨mL, x⟩)
          (Fus.rightFinalRow a b c d ⟨mR, y⟩) =
        ∑ z, Fus.fullInversePrintedFMatrix a b c
          (Fus.leftFinalRow a b c d ⟨mL, x⟩)
          (Fus.rightFinalRow a b c d ⟨mR, z⟩) * Fus.tensor d (i, k) z y := by
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single d
      (fun q _ hq => Finset.sum_eq_zero fun z _ => by
        rw [rightTripleDirectSumLetter, rightFinalRow,
          Matrix.blockDiagonal'_apply_ne _ _ _ hq, mul_zero])
      (fun h => absurd (Finset.mem_univ d) h)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single mR
      (fun q _ hq => Finset.sum_eq_zero fun z _ => by
        simp [rightTripleDirectSumLetter, leftFinalRow, rightFinalRow,
          Matrix.blockDiagonal'_apply_eq, hq])
      (fun h => absurd (Finset.mem_univ mR) h)]
    simp [rightTripleDirectSumLetter, leftFinalRow, rightFinalRow,
      Matrix.blockDiagonal'_apply_eq]
  have hSimple := hLeft.symm.trans (hEntry.trans hRight)
  simpa [Matrix.submatrix_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply] using hSimple

/-- The multiplicity matrix in the opposite orientation, obtained from the
fixed-final corner of $L_d^+R_d$. -/
noncomputable def inversePrintedFMatrix (a b c d : Λ) :
    Matrix (Fus.LeftTripleMultiplicity a b c d)
      (Fus.RightTripleMultiplicity a b c d) ℂ :=
  Classical.choose (Fus.exists_inverseCorner_eq_kronecker_one a b c d)

private theorem inverseCorner_eq_kronecker_one (a b c d : Λ) :
    (Fus.fullInversePrintedFMatrix a b c).submatrix
        (Fus.leftFinalRow a b c d) (Fus.rightFinalRow a b c d) =
      Fus.inversePrintedFMatrix a b c d ⊗ₖ
        (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) :=
  Classical.choose_spec (Fus.exists_inverseCorner_eq_kronecker_one a b c d)

/-- The printed matrix followed by the opposite comparison is the identity. -/
theorem printedFMatrix_mul_inversePrintedFMatrix (a b c d : Λ) :
    Fus.printedFMatrix a b c d * Fus.inversePrintedFMatrix a b c d = 1 := by
  apply Matrix.mul_eq_one_of_kronecker_one (Fus.bondDim_pos d)
  change (Fus.printedFMatrix a b c d ⊗ₖ
      (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) *
      (Fus.inversePrintedFMatrix a b c d ⊗ₖ
        (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) =
    (1 : Matrix
      (Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d))
      (Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d)) ℂ)
  have hFull := Fus.fullPrintedFMatrix_mul_fullInversePrintedFMatrix a b c
  rw [← Fus.printedFMatrixAmplified_eq_kronecker_one a b c d,
    ← Fus.inverseCorner_eq_kronecker_one a b c d]
  have hF (u : Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d))
      (v : Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d)) :
      Fus.fullPrintedFMatrix a b c ⟨d, u⟩ ⟨d, v⟩ =
        Fus.printedFMatrix a b c d u.1 v.1 *
          (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) u.2 v.2 := by
    simpa [printedFMatrixAmplified, Matrix.submatrix_apply, Matrix.kronecker_apply,
      rightFinalRow, leftFinalRow]
      using congrArg (fun M => M u v)
        (Fus.printedFMatrixAmplified_eq_kronecker_one a b c d)
  have hG (u : Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d))
      (v : Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d)) :
      Fus.fullInversePrintedFMatrix a b c ⟨d, u⟩ ⟨d, v⟩ =
        Fus.inversePrintedFMatrix a b c d u.1 v.1 *
          (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) u.2 v.2 := by
    simpa [Matrix.submatrix_apply, Matrix.kronecker_apply, rightFinalRow, leftFinalRow] using
      congrArg (fun M => M u v) (Fus.inverseCorner_eq_kronecker_one a b c d)
  funext x y
  rcases x with ⟨mx, bx⟩
  rcases y with ⟨my, byy⟩
  let x : Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d) := ⟨mx, bx⟩
  let y : Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d) := ⟨my, byy⟩
  have hEntry := congrArg
    (fun M => M (Fus.rightFinalRow a b c d x) (Fus.rightFinalRow a b c d y)) hFull
  rw [Matrix.mul_apply, Fintype.sum_sigma] at hEntry
  rw [Finset.sum_eq_single d
    (fun e _ hed => Finset.sum_eq_zero fun q _ => by
      have hZero : Fus.fullPrintedFMatrix a b c
          (Fus.rightFinalRow a b c d x) ⟨e, q⟩ = 0 := by
        simpa [Matrix.submatrix_apply, rightFinalRow, leftFinalRow] using
          congrArg (fun M => M x q)
            (Fus.fullPrintedFMatrix_finalSector_eq_zero a b c d e (Ne.symm hed))
      rw [hZero, zero_mul])
    (fun hmem => absurd (Finset.mem_univ d) hmem)] at hEntry
  rw [Matrix.mul_apply]
  have hOne :
      (1 : Matrix (Fus.RightTripleIndex a b c) (Fus.RightTripleIndex a b c) ℂ)
          (Fus.rightFinalRow a b c d x) (Fus.rightFinalRow a b c d y) =
        (1 : Matrix
          (Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d))
          (Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d)) ℂ) x y := by
    simp [rightFinalRow, Matrix.one_apply, x, y]
  rw [hOne] at hEntry
  exact hEntry

/-- The opposite comparison followed by the printed matrix is the identity. -/
theorem inversePrintedFMatrix_mul_printedFMatrix (a b c d : Λ) :
    Fus.inversePrintedFMatrix a b c d * Fus.printedFMatrix a b c d = 1 := by
  apply Matrix.mul_eq_one_of_kronecker_one (Fus.bondDim_pos d)
  change (Fus.inversePrintedFMatrix a b c d ⊗ₖ
      (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) *
      (Fus.printedFMatrix a b c d ⊗ₖ
        (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) =
    (1 : Matrix
      (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d))
      (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d)) ℂ)
  have hFull := Fus.fullInversePrintedFMatrix_mul_fullPrintedFMatrix a b c
  rw [← Fus.inverseCorner_eq_kronecker_one a b c d,
    ← Fus.printedFMatrixAmplified_eq_kronecker_one a b c d]
  have hF (u : Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d))
      (v : Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d)) :
      Fus.fullPrintedFMatrix a b c ⟨d, u⟩ ⟨d, v⟩ =
        Fus.printedFMatrix a b c d u.1 v.1 *
          (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) u.2 v.2 := by
    simpa [printedFMatrixAmplified, Matrix.submatrix_apply, Matrix.kronecker_apply,
      rightFinalRow, leftFinalRow]
      using congrArg (fun M => M u v)
        (Fus.printedFMatrixAmplified_eq_kronecker_one a b c d)
  have hG (u : Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d))
      (v : Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d)) :
      Fus.fullInversePrintedFMatrix a b c ⟨d, u⟩ ⟨d, v⟩ =
        Fus.inversePrintedFMatrix a b c d u.1 v.1 *
          (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) u.2 v.2 := by
    simpa [Matrix.submatrix_apply, Matrix.kronecker_apply, rightFinalRow, leftFinalRow] using
      congrArg (fun M => M u v) (Fus.inverseCorner_eq_kronecker_one a b c d)
  funext x y
  rcases x with ⟨mx, bx⟩
  rcases y with ⟨my, byy⟩
  let x : Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d) := ⟨mx, bx⟩
  let y : Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d) := ⟨my, byy⟩
  have hEntry := congrArg
    (fun M => M (Fus.leftFinalRow a b c d x) (Fus.leftFinalRow a b c d y)) hFull
  rw [Matrix.mul_apply, Fintype.sum_sigma] at hEntry
  rw [Finset.sum_eq_single d
    (fun e _ hed => Finset.sum_eq_zero fun q _ => by
      have hZero : Fus.fullPrintedFMatrix a b c ⟨e, q⟩
          (Fus.leftFinalRow a b c d y) = 0 := by
        simpa [Matrix.submatrix_apply, rightFinalRow, leftFinalRow] using
          congrArg (fun M => M q y)
            (Fus.fullPrintedFMatrix_finalSector_eq_zero a b c e d hed)
      rw [hZero, mul_zero])
    (fun hmem => absurd (Finset.mem_univ d) hmem)] at hEntry
  rw [Matrix.mul_apply]
  have hOne :
      (1 : Matrix (Fus.LeftTripleIndex a b c) (Fus.LeftTripleIndex a b c) ℂ)
          (Fus.leftFinalRow a b c d x) (Fus.leftFinalRow a b c d y) =
        (1 : Matrix
          (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d))
          (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d)) ℂ) x y := by
    simp [leftFinalRow, Matrix.one_apply, x, y]
  rw [hOne] at hEntry
  exact hEntry

end MPOTensor.CompleteZipperFusionFamily

end

section

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

end
