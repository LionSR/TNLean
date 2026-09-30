/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SwapMatrix
import TNLean.MPS.MPU.Examples.ShiftSourceBlockedFormulas
import TNLean.MPS.MPU.TwoSiteStandardForm

/-!
# Explicit standard forms of the shift families

The supplied gates and half factors realize CPSV17, equations `eq:SF_u1_u3`,
`eq:uv2_U2`, and `eq:uv2_U3` (lines 2009–2034).
-/

open scoped Matrix

namespace MPOTensor

/-- The identity family has identity gates (CPSV17, `eq:SF_u1_u3`). -/
noncomputable def shiftExampleU₁StandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (shiftExampleU₁ d)
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) 1 := by
  classical
  refine {
    phys_pos := NeZero.pos d
    bond_pos := by decide
    left_pos := NeZero.pos d
    right_pos := NeZero.pos d
    X₁ := fun i r => if i.1 = r then 1 else 0
    X₂ := fun i l => if i.2 = l then 1 else 0
    u_unitary := ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
    v_unitary := ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
    v_apply := ?_
    W_apply := ?_
  }
  · intro i₁ i₂ s t
    by_cases h₁ : i₁ = s <;> by_cases h₂ : i₂ = t <;> simp [Matrix.one_apply, h₁, h₂]
  · intro i j α γ
    have hαγ : α = γ := Subsingleton.elim _ _
    simp [shiftExampleU₁, identityMPUTensor, tensorProduct, idTensor,
      Matrix.reindex_apply, Matrix.one_apply,
      Prod.mk.injEq, ite_and, apply_ite]
    split_ifs <;> simp_all

/-- The counterpropagating family has swap gates (CPSV17, `eq:SF_u1_u3`). -/
noncomputable def shiftExampleU₃StandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (shiftExampleU₃ d) (Matrix.swapMatrix d)
      (Matrix.swapMatrix d) := by
  classical
  refine {
    phys_pos := NeZero.pos d
    bond_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    left_pos := NeZero.pos d
    right_pos := NeZero.pos d
    X₁ := fun i r => if i.2.divNat = r ∧ i.2.modNat = i.1 then 1 else 0
    X₂ := fun i l => if i.1.divNat = i.2 ∧ i.1.modNat = l then 1 else 0
    u_unitary := Matrix.swapMatrix_isUnitaryBetween d
    v_unitary := Matrix.swapMatrix_isUnitaryBetween d
    v_apply := ?_
    W_apply := ?_
  }
  · intro i₁ i₂ s t
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp [Matrix.swapMatrix, Fintype.sum_prod_type, ite_and, eq_comm]
    split_ifs <;> simp_all
  · intro i j α γ
    simp [shiftExampleU₃, tensorProduct, rightShiftTensor, leftShiftTensor,
      physicalAdjointTensor, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.single, Matrix.swapMatrix, ite_and, eq_comm]
    split_ifs <;> simp_all


private theorem identitySwapIdentityMatrix_isUnitaryBetween (d : ℕ) :
    (identitySwapIdentityMatrix d).IsUnitaryBetween := by
  change (_ᴴ * _ = 1) ∧ (_ * _ᴴ = 1)
  constructor <;> ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩ <;>
    simp [Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, identitySwapIdentityMatrix,
      Matrix.one_apply, Prod.mk.injEq, ite_and, eq_comm]
  all_goals split_ifs <;> simp_all

private theorem swapTensorSwapMatrix_isUnitaryBetween (d : ℕ) :
    (swapTensorSwapMatrix d).IsUnitaryBetween := by
  change (_ᴴ * _ = 1) ∧ (_ * _ᴴ = 1)
  constructor <;> ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩ <;>
    simp [Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      swapTensorSwapMatrix_apply, Matrix.one_apply, Prod.mk.injEq, ite_and, eq_comm]
  all_goals split_ifs <;> simp_all


/-- The first counterpropagating family after two-site blocking, with the
four-spin gates of CPSV17, equation `eq:uv2_U2`, lines 2021–2026. -/
noncomputable def shiftExampleU₂BlockedStandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (blockTwo (shiftExampleU₂ d))
      (Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
        (identitySwapIdentityMatrix d))
      (Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
        (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)) := by
  classical
  refine {
    phys_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    bond_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    left_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    right_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    X₁ := fun i r => if i.2.divNat = i.1.divNat ∧
      i.1.modNat = r.divNat ∧ i.2.modNat = r.modNat then 1 else 0
    X₂ := fun i l => if i.1.divNat = l.divNat ∧
      i.2.divNat = l.modNat ∧ i.1.modNat = i.2.modNat then 1 else 0
    u_unitary := (identitySwapIdentityMatrix_isUnitaryBetween d).reindex _ _ _
    v_unitary := ((swapTensorSwapMatrix_isUnitaryBetween d).mul _ _
      (identitySwapIdentityMatrix_isUnitaryBetween d)).reindex _ _ _
    v_apply := ?_
    W_apply := ?_
  }
  · intro i₁ i₂ r l
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp [Matrix.reindex_apply, shiftTwoSitePhysicalEquiv,
      Fintype.sum_prod_type, ite_and, eq_comm]
    split_ifs <;> simp_all
  · intro i j α γ
    simp only [blockTwo, Matrix.mul_apply]
    simp_rw [← Equiv.sum_comp finProdFinEquiv]
    simp [shiftExampleU₂, tensorProduct, rightShiftTensor, leftShiftTensor,
      physicalAdjointTensor, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.single, shiftTwoSitePhysicalEquiv, Fintype.sum_prod_type,
      ite_and, eq_comm]
    split_ifs <;> simp_all [eq_comm]

/-- The reversed family after two-site blocking, with the four-spin gates
of CPSV17, equation `eq:uv2_U3`, lines 2030–2034. -/
noncomputable def shiftExampleU₃BlockedStandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (blockTwo (shiftExampleU₃ d))
      (Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
        (identitySwapIdentityMatrix d * swapTensorSwapMatrix d))
      (Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
        (identitySwapIdentityMatrix d)) := by
  classical
  refine {
    phys_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    bond_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    left_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    right_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    X₁ := fun i r => if i.2.divNat = r.modNat ∧
      i.1.divNat = r.divNat ∧ i.2.modNat = i.1.modNat then 1 else 0
    X₂ := fun i l => if i.1.divNat = i.2.divNat ∧
      i.1.modNat = l.divNat ∧ i.2.modNat = l.modNat then 1 else 0
    u_unitary := ((identitySwapIdentityMatrix_isUnitaryBetween d).mul _ _
      (swapTensorSwapMatrix_isUnitaryBetween d)).reindex _ _ _
    v_unitary := (identitySwapIdentityMatrix_isUnitaryBetween d).reindex _ _ _
    v_apply := ?_
    W_apply := ?_
  }
  · intro i₁ i₂ r l
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp [Matrix.reindex_apply, shiftTwoSitePhysicalEquiv,
      Fintype.sum_prod_type, ite_and, eq_comm]
    split_ifs <;> simp_all
  · intro i j α γ
    simp only [blockTwo, Matrix.mul_apply]
    simp_rw [← Equiv.sum_comp finProdFinEquiv]
    simp [shiftExampleU₃, tensorProduct, rightShiftTensor, leftShiftTensor,
      physicalAdjointTensor, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.single, shiftTwoSitePhysicalEquiv, Fintype.sum_prod_type,
      ite_and, eq_comm]
    split_ifs <;> simp_all [eq_comm]

end MPOTensor
