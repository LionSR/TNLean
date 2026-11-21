/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.MPDO.CommutingForm

/-!
# Two-site cyclic window placements in pair coordinates

On a periodic chain of length two, the placement on the window beginning at
site zero preserves the order of the two physical indices, while the placement
on the window beginning at site one exchanges them. These identities hold for an arbitrary two-site
matrix.
-/

open ManyBody

namespace MPOTensor

variable {d : ℕ}

/-! ### Agreement outside a length-two window on a three-site chain

In right-associated triple coordinates, two configurations agree outside a
length-two window exactly when their coordinate outside the window coincides.
These characterizations are reused by the three-site window-placement
identifications for both the physical-sector and isometric transports. -/

/-- In right-associated triple coordinates, agreement outside a length-two
window starting at the first site holds exactly when the third coordinates
coincide. -/
theorem forall_ringWindow_ne_imp_finThreeArrowEquiv_three_zero
    (σ τ : Fin d × (Fin d × Fin d)) :
    (∀ v, (∀ u, ringWindow (by decide : 2 ≤ 3) (0 : Fin 3) u ≠ v) →
        (_root_.finThreeArrowEquiv (Fin d)).symm σ v =
          (_root_.finThreeArrowEquiv (Fin d)).symm τ v) ↔
      τ.2.2 = σ.2.2 := by
  rw [MPSTensor.forall_ringWindow_ne_imp_iff_replaceWindow]
  constructor
  · intro ha
    have h := congrFun ha (2 : Fin 3)
    simpa [MPSTensor.replaceWindow, MPSTensor.extractWindow] using h
  · intro ha
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow, ha]

/-- In right-associated triple coordinates, agreement outside a length-two
window starting at the second site holds exactly when the first coordinates
coincide. -/
theorem forall_ringWindow_ne_imp_finThreeArrowEquiv_three_one
    (σ τ : Fin d × (Fin d × Fin d)) :
    (∀ v, (∀ u, ringWindow (by decide : 2 ≤ 3) (1 : Fin 3) u ≠ v) →
        (_root_.finThreeArrowEquiv (Fin d)).symm σ v =
          (_root_.finThreeArrowEquiv (Fin d)).symm τ v) ↔
      τ.1 = σ.1 := by
  rw [MPSTensor.forall_ringWindow_ne_imp_iff_replaceWindow]
  constructor
  · intro ha
    have h := congrFun ha (0 : Fin 3)
    simpa [MPSTensor.replaceWindow, MPSTensor.extractWindow] using h
  · intro ha
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow, ha]

/-- In pair coordinates, placing an arbitrary two-site matrix at site zero
preserves its physical-index order. -/
theorem reindex_placeAlong_ringWindow_two_zero
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
        (_root_.finTwoArrowEquiv (Fin d))
        (placeAlong (X := fun _ ↦ Fin d) (ringWindow le_rfl (0 : Fin 2)) B) =
      Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
        (_root_.finTwoArrowEquiv (Fin d)) B := by
  ext σ τ
  have hAgree : ∀ v, (∀ u, ringWindow le_rfl (0 : Fin 2) u ≠ v) →
      (_root_.finTwoArrowEquiv (Fin d)).symm σ v =
        (_root_.finTwoArrowEquiv (Fin d)).symm τ v := by
    rw [MPSTensor.forall_ringWindow_ne_imp_iff_replaceWindow]
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow,
        _root_.finTwoArrowEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [placeAlong_apply]
  rw [ite_eq_left hAgree]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply]
  congr 1 <;> funext j <;> fin_cases j <;> rfl

/-- In pair coordinates, placing an arbitrary two-site matrix at site one
exchanges its two physical indices. -/
theorem reindex_placeAlong_ringWindow_two_one
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
        (_root_.finTwoArrowEquiv (Fin d))
        (placeAlong (X := fun _ ↦ Fin d) (ringWindow le_rfl (1 : Fin 2)) B) =
      Matrix.reindex (Equiv.prodComm (Fin d) (Fin d))
        (Equiv.prodComm (Fin d) (Fin d))
        (Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
          (_root_.finTwoArrowEquiv (Fin d)) B) := by
  ext σ τ
  have hAgree : ∀ v, (∀ u, ringWindow le_rfl (1 : Fin 2) u ≠ v) →
      (_root_.finTwoArrowEquiv (Fin d)).symm σ v =
        (_root_.finTwoArrowEquiv (Fin d)).symm τ v := by
    rw [MPSTensor.forall_ringWindow_ne_imp_iff_replaceWindow]
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow,
        _root_.finTwoArrowEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [placeAlong_apply]
  rw [ite_eq_left hAgree]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply]
  congr 1 <;> funext j <;> fin_cases j <;> rfl

end MPOTensor
