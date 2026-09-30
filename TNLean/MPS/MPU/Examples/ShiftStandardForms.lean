/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SwapMatrix
import TNLean.MPS.MPU.Examples.ShiftSwapMatrices
import TNLean.MPS.MPU.Examples.ShiftTilde
import TNLean.MPS.MPU.TwoSiteStandardForm

/-!
# Explicit standard forms of the shift families

The supplied gates and half factors realize CPSV17, equations `eq:SF_u1_u3`,
`eq:uv2_U2`, and `eq:uv2_U3` (lines 2009–2034). The first two swap-transformed
families realize the gates in `SFu1u3` (lines 2090–2099).

These data prove the gate unitarity and open contractions. They do not yet
identify the half factors with the trace-normalized supplied source factors;
that remaining requirement of #7028 is separate from these contractions.
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
    v_unitary :=
      (swapTensorSwapMatrix_mul_identitySwapIdentityMatrix_isUnitaryBetween d).reindex _ _ _
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
    u_unitary :=
      (identitySwapIdentityMatrix_mul_swapTensorSwapMatrix_isUnitaryBetween d).reindex _ _ _
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

private theorem ketLeftMul_shiftPhysicalSwap_apply {d D : ℕ}
    (U : MPOTensor (d * d) D) (i j : Fin (d * d)) (α β : Fin D) :
    U.ketLeftMul (shiftPhysicalSwap d) i j α β =
      U (finProdFinEquiv (i.modNat, i.divNat)) j α β := by
  simp [ketLeftMul, shiftPhysicalSwap, Equiv.Perm.permMatrix, PEquiv.toMatrix,
    bondPairSwapEquiv, bondPairSwap, Matrix.sum_apply, Matrix.ite_apply]

/-- The swap-transformed identity family has a swap gate followed by an
identity gate (CPSV17, `SFu1u3`, lines 2090–2099). -/
noncomputable def shiftExampleTildeU₁StandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (shiftExampleTildeU₁ d) (Matrix.swapMatrix d)
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  classical
  let S := shiftExampleU₁StandardForm d
  refine {
    phys_pos := S.phys_pos
    bond_pos := S.bond_pos
    left_pos := S.left_pos
    right_pos := S.right_pos
    X₁ := S.X₁
    X₂ := S.X₂
    u_unitary := Matrix.swapMatrix_isUnitaryBetween d
    v_unitary := S.v_unitary
    v_apply := S.v_apply
    W_apply := ?_
  }
  intro i j α γ
  have hαγ : α = γ := Subsingleton.elim _ _
  rw [shiftExampleTildeU₁, ketLeftMul_shiftPhysicalSwap_apply]
  simp [S, shiftExampleU₁StandardForm, shiftExampleU₁, identityMPUTensor,
    tensorProduct, idTensor, Matrix.reindex_apply,
    Matrix.swapMatrix, ite_and, apply_ite]
  split_ifs <;> simp_all

/-- The swap-transformed second family has an identity gate followed by a
swap gate (CPSV17, `SFu1u3`, lines 2090–2099). -/
noncomputable def shiftExampleTildeU₂StandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (shiftExampleTildeU₂ d)
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (Matrix.swapMatrix d) := by
  classical
  refine {
    phys_pos := NeZero.pos d
    bond_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    left_pos := NeZero.pos d
    right_pos := NeZero.pos d
    X₁ := fun i r => if i.2.divNat = i.1 ∧ i.2.modNat = r then 1 else 0
    X₂ := fun i l => if i.1.divNat = l ∧ i.1.modNat = i.2 then 1 else 0
    u_unitary := ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
    v_unitary := Matrix.swapMatrix_isUnitaryBetween d
    v_apply := ?_
    W_apply := ?_
  }
  · intro i₁ i₂ r l
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp [Matrix.swapMatrix, Fintype.sum_prod_type, ite_and, eq_comm]
  · intro i j α γ
    rw [shiftExampleTildeU₂, ketLeftMul_shiftPhysicalSwap_apply]
    simp [shiftExampleU₂, tensorProduct, rightShiftTensor, leftShiftTensor,
      physicalAdjointTensor, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.single, Matrix.one_apply, Prod.mk.injEq, ite_and, eq_comm]
    split_ifs <;> simp_all

end MPOTensor
