/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingForm

/-!
# Two-site cyclic local embeddings in pair coordinates

On a periodic chain of length two, the local embedding beginning at site zero
preserves the order of the two physical indices, while the embedding beginning
at site one exchanges them. These identities hold for an arbitrary two-site
matrix.
-/

namespace MPOTensor

variable {d : ℕ}

/-- In pair coordinates, embedding an arbitrary two-site matrix at site zero
preserves its physical-index order. -/
theorem reindex_embedLocalOperator_two_zero
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
        (_root_.finTwoArrowEquiv (Fin d))
        (embedLocalOperator (d := d) 2 2 (by decide) (0 : Fin 2) B) =
      Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
        (_root_.finTwoArrowEquiv (Fin d)) B := by
  ext σ τ
  have hAgree : AgreesOutsideWindow (d := d) 2 (by decide) (0 : Fin 2)
      ((_root_.finTwoArrowEquiv (Fin d)).symm σ)
      ((_root_.finTwoArrowEquiv (Fin d)).symm τ) := by
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow,
        _root_.finTwoArrowEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply]
  rw [if_pos hAgree]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply]
  congr 1 <;> funext j <;> fin_cases j <;> rfl

/-- In pair coordinates, embedding an arbitrary two-site matrix at site one
exchanges its two physical indices. -/
theorem reindex_embedLocalOperator_two_one
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
        (_root_.finTwoArrowEquiv (Fin d))
        (embedLocalOperator (d := d) 2 2 (by decide) (1 : Fin 2) B) =
      Matrix.reindex (Equiv.prodComm (Fin d) (Fin d))
        (Equiv.prodComm (Fin d) (Fin d))
        (Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
          (_root_.finTwoArrowEquiv (Fin d)) B) := by
  ext σ τ
  have hAgree : AgreesOutsideWindow (d := d) 2 (by decide) (1 : Fin 2)
      ((_root_.finTwoArrowEquiv (Fin d)).symm σ)
      ((_root_.finTwoArrowEquiv (Fin d)).symm τ) := by
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow,
        _root_.finTwoArrowEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply]
  rw [if_pos hAgree]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply]
  congr 1 <;> funext j <;> fin_cases j <;> rfl

end MPOTensor
