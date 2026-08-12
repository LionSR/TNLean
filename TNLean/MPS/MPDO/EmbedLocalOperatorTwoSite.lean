/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
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

/-! ### Agreement outside a length-two window on a three-site chain

In right-associated triple coordinates, two configurations agree outside a
length-two window exactly when their coordinate outside the window coincides.
These characterizations are reused by the three-site local-embedding
identifications for both the physical-sector and isometric transports. -/

/-- In right-associated triple coordinates, agreement outside a length-two
window starting at the first site holds exactly when the third coordinates
coincide. -/
theorem agreesOutsideWindow_finThreeArrowEquiv_three_zero
    (σ τ : Fin d × (Fin d × Fin d)) :
    AgreesOutsideWindow (d := d) 2 (by decide) (0 : Fin 3)
        ((_root_.finThreeArrowEquiv (Fin d)).symm σ)
        ((_root_.finThreeArrowEquiv (Fin d)).symm τ) ↔
      τ.2.2 = σ.2.2 := by
  constructor
  · intro ha
    have h := congrFun ha (2 : Fin 3)
    simpa [AgreesOutsideWindow, MPSTensor.replaceWindow,
      MPSTensor.extractWindow] using h
  · intro ha
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow, ha]

/-- In right-associated triple coordinates, agreement outside a length-two
window starting at the second site holds exactly when the first coordinates
coincide. -/
theorem agreesOutsideWindow_finThreeArrowEquiv_three_one
    (σ τ : Fin d × (Fin d × Fin d)) :
    AgreesOutsideWindow (d := d) 2 (by decide) (1 : Fin 3)
        ((_root_.finThreeArrowEquiv (Fin d)).symm σ)
        ((_root_.finThreeArrowEquiv (Fin d)).symm τ) ↔
      τ.1 = σ.1 := by
  constructor
  · intro ha
    have h := congrFun ha (0 : Fin 3)
    simpa [MPSTensor.replaceWindow, MPSTensor.extractWindow] using h
  · intro ha
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow, ha]

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
