/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.ActionTensor

/-!
# Triangular physical padding of operator and state tensors

An operator tensor occupies the upper-left physical corner of an alphabet
with one additional letter. A state tensor occupies the upper-right physical
column. These embeddings preserve the virtual bonds and turn operator
multiplication and operator action into multiplication of operator tensors.
Every product with a state tensor on the left vanishes.

This is an auxiliary coordinate construction for the fusion and action
tensors of Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels`,
`eq:F_symbol2`, and `coupledpent`. It imposes no additional tensor equations.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d D D₁ D₂ : ℕ}

/-- Place an operator tensor in the upper-left physical corner, with a zero
last physical row and column. The virtual bond dimension is unchanged. -/
def operatorPhysicalPadding (O : MPOTensor d D) : MPOTensor (d + 1) D :=
  fun i j ↦ Fin.lastCases 0 (fun i ↦ Fin.lastCases 0 (fun j ↦ O i j) j) i

/-- Place a state tensor in the last physical column, above a zero last row.
The virtual bond dimension is unchanged. -/
def statePhysicalPadding (A : MPSTensor d D) : MPOTensor (d + 1) D :=
  fun i j ↦ Fin.lastCases 0 (fun i ↦ Fin.lastCases (A i) (fun _ ↦ 0) j) i

/-- The retained physical corner is the original operator tensor. -/
@[simp] theorem operatorPhysicalPadding_castSucc_castSucc (O : MPOTensor d D)
    (i j : Fin d) : operatorPhysicalPadding O i.castSucc j.castSucc = O i j := by
  simp [operatorPhysicalPadding]

/-- The last physical row of a padded operator vanishes. -/
@[simp] theorem operatorPhysicalPadding_last (O : MPOTensor d D) (j : Fin (d + 1)) :
    operatorPhysicalPadding O (Fin.last d) j = 0 := by
  simp [operatorPhysicalPadding]

/-- The last physical column of a padded operator vanishes. -/
@[simp] theorem operatorPhysicalPadding_last_right (O : MPOTensor d D)
    (i : Fin (d + 1)) : operatorPhysicalPadding O i (Fin.last d) = 0 := by
  cases i using Fin.lastCases <;> simp [operatorPhysicalPadding]

/-- The retained part of the last physical column is the original state tensor. -/
@[simp] theorem statePhysicalPadding_castSucc_last (A : MPSTensor d D) (i : Fin d) :
    statePhysicalPadding A i.castSucc (Fin.last d) = A i := by
  simp [statePhysicalPadding]

/-- Every original physical column of a padded state vanishes. -/
@[simp] theorem statePhysicalPadding_castSucc_right (A : MPSTensor d D)
    (i : Fin (d + 1)) (j : Fin d) : statePhysicalPadding A i j.castSucc = 0 := by
  cases i using Fin.lastCases <;> simp [statePhysicalPadding]

/-- The last physical row of a padded state vanishes. -/
@[simp] theorem statePhysicalPadding_last (A : MPSTensor d D) (j : Fin (d + 1)) :
    statePhysicalPadding A (Fin.last d) j = 0 := by
  simp [statePhysicalPadding]

/-- Upper-left physical padding preserves operator multiplication, including
the original flattening of the product virtual bond. -/
theorem mulTensor_operatorPhysicalPadding (O : MPOTensor d D₁) (P : MPOTensor d D₂) :
    mulTensor (operatorPhysicalPadding O) (operatorPhysicalPadding P) =
      operatorPhysicalPadding (mulTensor O P) := by
  funext i k
  cases i using Fin.lastCases <;> cases k using Fin.lastCases <;>
    simp [mulTensor, Fin.sum_univ_castSucc]

/-- Multiplying a padded operator by a padded state is the padded action
tensor, with the original operator-state virtual bond. -/
theorem mulTensor_operatorPhysicalPadding_statePhysicalPadding
    (O : MPOTensor d D₁) (A : MPSTensor d D₂) :
    mulTensor (operatorPhysicalPadding O) (statePhysicalPadding A) =
      statePhysicalPadding (actTensor O A) := by
  funext i k
  cases i using Fin.lastCases <;> cases k using Fin.lastCases <;>
    simp [mulTensor, actTensor, Fin.sum_univ_castSucc]

/-- A padded state followed by a padded operator has no matching physical
contraction index and therefore vanishes. -/
theorem mulTensor_statePhysicalPadding_operatorPhysicalPadding
    (A : MPSTensor d D₁) (O : MPOTensor d D₂) :
    mulTensor (statePhysicalPadding A) (operatorPhysicalPadding O) = 0 := by
  funext i k
  simp [mulTensor, Fin.sum_univ_castSucc]

/-- Two padded states have no matching physical contraction index, so their
operator product vanishes. -/
theorem mulTensor_statePhysicalPadding_statePhysicalPadding
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    mulTensor (statePhysicalPadding A) (statePhysicalPadding B) = 0 := by
  funext i k
  simp [mulTensor, Fin.sum_univ_castSucc]

/-- Retaining every original operator letter preserves injectivity. -/
theorem isInjective_operatorPhysicalPadding {O : MPOTensor d D}
    (hO : Kraus.IsInjective O.toMPSTensor) :
    Kraus.IsInjective (operatorPhysicalPadding O).toMPSTensor := by
  unfold Kraus.IsInjective
  apply top_unique
  rw [← hO.span_eq_top]
  apply Submodule.span_mono
  rintro X ⟨q, rfl⟩
  refine ⟨finProdFinEquiv (q.divNat.castSucc, q.modNat.castSucc), ?_⟩
  simp [toMPSTensor]

/-- Retaining every original state letter preserves injectivity. -/
theorem isInjective_statePhysicalPadding {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) :
    Kraus.IsInjective (statePhysicalPadding A).toMPSTensor := by
  unfold Kraus.IsInjective
  apply top_unique
  rw [← hA.span_eq_top]
  apply Submodule.span_mono
  rintro X ⟨i, rfl⟩
  refine ⟨finProdFinEquiv (i.castSucc, Fin.last d), ?_⟩
  simp [toMPSTensor]

end MPOTensor
