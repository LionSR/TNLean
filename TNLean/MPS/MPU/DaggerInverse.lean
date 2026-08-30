/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.GroupRepresentation
import TNLean.MPS.MPDO.PhysicalAdjoint

/-!
# Physical adjoints and inverses in MPU representations

This file identifies the physical adjoint of a represented MPU tensor with the
tensor representing the inverse group element at the periodic-operator and
positive-length matrix product vector levels.

## Main results

* `MPOTensor.GroupFamily.IsRepresentation.mpo_physicalAdjointTensor_eq_inv`:
  the physical adjoint for `g` generates the operator represented by `g⁻¹`.
* `MPOTensor.GroupFamily.IsRepresentation.sameMPV₂Pos_physicalAdjointTensor_inv`:
  the corresponding underlying MPS tensors generate the same positive-length
  matrix product vectors.

Source: arXiv:2502.20257, line 1552.
-/

open scoped Matrix

namespace MPOTensor.GroupFamily

universe u

variable {G : Type u} {d : ℕ}

/-- The physical adjoint of the tensor representing `g` generates the operator
represented by `g⁻¹` on every nonempty chain.

This is the operator-level assertion preceding the virtual-gauge construction
in arXiv:2502.20257, line 1552. -/
theorem IsRepresentation.mpo_physicalAdjointTensor_eq_inv [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (g : G) (N : ℕ) (hN : 0 < N) :
    MPOTensor.mpo (MPOTensor.physicalAdjointTensor (F.tensor g)) N =
      MPOTensor.mpo (F.tensor g⁻¹) N := by
  have hInvMul :
      MPOTensor.mpo (F.tensor g⁻¹) N * MPOTensor.mpo (F.tensor g) N = 1 := by
    rw [hF.operator_mul g⁻¹ g N hN, inv_mul_cancel, hF.operator_one N hN]
  have hUnit :
      MPOTensor.mpo (F.tensor g) N * star (MPOTensor.mpo (F.tensor g) N) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (hF.isMPUPos g N hN)
  have hInvEqStar :
      MPOTensor.mpo (F.tensor g⁻¹) N = star (MPOTensor.mpo (F.tensor g) N) := by
    calc
      MPOTensor.mpo (F.tensor g⁻¹) N =
          MPOTensor.mpo (F.tensor g⁻¹) N * 1 := (mul_one _).symm
      _ = MPOTensor.mpo (F.tensor g⁻¹) N *
          (MPOTensor.mpo (F.tensor g) N * star (MPOTensor.mpo (F.tensor g) N)) := by
            rw [hUnit]
      _ = (MPOTensor.mpo (F.tensor g⁻¹) N * MPOTensor.mpo (F.tensor g) N) *
          star (MPOTensor.mpo (F.tensor g) N) := by rw [mul_assoc]
      _ = star (MPOTensor.mpo (F.tensor g) N) := by rw [hInvMul, one_mul]
  ext σ τ
  rw [MPOTensor.mpo_physicalAdjointTensor]
  exact (congrFun (congrFun hInvEqStar σ) τ).symm

/-- The physical-adjoint tensor for `g` and the tensor for `g⁻¹` generate the
same matrix product vectors at every positive length.

Source: arXiv:2502.20257, line 1552. -/
theorem IsRepresentation.sameMPV₂Pos_physicalAdjointTensor_inv [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation) (g : G) :
    MPSTensor.SameMPV₂Pos
      (MPOTensor.physicalAdjointTensor (F.tensor g)).toMPSTensor
      (F.tensor g⁻¹).toMPSTensor := by
  intro N hN ρ
  let σ : Fin N → Fin d := fun n ↦ (ρ n).divNat
  let τ : Fin N → Fin d := fun n ↦ (ρ n).modNat
  have hρ : (fun n ↦ finProdFinEquiv (σ n, τ n)) = ρ := by
    funext n
    exact finProdFinEquiv.apply_symm_apply (ρ n)
  rw [← hρ, MPSTensor.mpv_toMPSTensor_pairConfig,
    MPSTensor.mpv_toMPSTensor_pairConfig,
    hF.mpo_physicalAdjointTensor_eq_inv F g N hN]

end MPOTensor.GroupFamily
