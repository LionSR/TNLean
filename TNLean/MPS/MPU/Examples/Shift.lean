/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceUContraction
import TNLean.MPS.MPU.TensorProduct
import TNLean.MPS.MPDO.StackedLayers
import TNLean.MPS.MPDO.AreaLaw
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Shift matrix product unitaries

The examples in arXiv:1703.09188, lines 1980--2001.
-/

open scoped Matrix Kronecker

namespace MPOTensor

/-- The bond-`d` tensor whose closed MPO is the right shift. -/
def rightShiftTensor (d : ℕ) : MPOTensor d d :=
  fun i j ↦ Matrix.single i j 1

@[simp] theorem rightShiftTensor_apply (d : ℕ) (i j α β : Fin d) :
    rightShiftTensor d i j α β = if i = α ∧ j = β then 1 else 0 := by
  rfl

/-- Entry formula fixing the row convention: Mathlib's permutation matrix for
`rotateConfig` is exactly the source right shift. -/
theorem mpo_rightShiftTensor_apply (d N : ℕ) [NeZero N]
    (σ τ : Fin N → Fin d) :
    mpo (rightShiftTensor d) N σ τ =
      Equiv.Perm.permMatrix ℂ (rotateConfig N d) σ τ := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  have h := MPSTensor.trace_evalWord_eq_sum_cyclic
    (rightShiftTensor d).toMPSTensor
    (fun n ↦ finProdFinEquiv (σ n, τ n))
  rw [MPSTensor.evalWord_ofFn_eq_prod] at h
  have h' :
      (List.ofFn fun i ↦ rightShiftTensor d (σ i) (τ i)).prod.trace =
        ∑ g : Fin N → Fin d, ∏ v : Fin N,
          rightShiftTensor d (σ v) (τ v) (g v) (g (v + 1)) := by
    simpa only [toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat] using h
  rw [h']
  by_cases hστ : rotateConfig N d σ = τ
  · rw [Fintype.sum_eq_single σ]
    · have hp : ∀ n, τ n = σ (n + 1) := by
        intro n
        simpa only [rotateConfig_apply, Function.comp_apply, finRotate_apply]
          using (congrFun hστ n).symm
      have hcomp : σ ∘ finRotate N = τ := by
        simpa only [rotateConfig_apply] using hστ
      simp [rightShiftTensor, hp, Equiv.Perm.permMatrix,
        PEquiv.toMatrix, hcomp]
    · intro g hg
      obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
      apply Finset.prod_eq_zero (Finset.mem_univ n)
      simp [rightShiftTensor, hn.symm]
  · have hcomp : σ ∘ finRotate N ≠ τ := by
      simpa only [rotateConfig_apply] using hστ
    have hrhs : Equiv.Perm.permMatrix ℂ (rotateConfig N d) σ τ = 0 := by
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, hcomp]
    rw [hrhs]
    apply Finset.sum_eq_zero
    intro g _
    by_cases hg : g = σ
    · subst g
      have hpoint : ∃ n, σ (n + 1) ≠ τ n := by
        simpa only [rotateConfig_apply, Function.comp_apply, finRotate_apply,
          ne_eq] using Function.ne_iff.mp hστ
      obtain ⟨n, hn⟩ := hpoint
      apply Finset.prod_eq_zero (Finset.mem_univ n)
      simp [rightShiftTensor, hn.symm]
    · obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
      apply Finset.prod_eq_zero (Finset.mem_univ n)
      simp [rightShiftTensor, hn.symm]

/-- The bond-`d` tensor generates the source right shift on every nonempty chain. -/
theorem mpo_rightShiftTensor (d N : ℕ) [NeZero N] :
    mpo (rightShiftTensor d) N = Equiv.Perm.permMatrix ℂ (rotateConfig N d) := by
  ext σ τ
  exact mpo_rightShiftTensor_apply d N σ τ

/-- The right-shift tensor is an MPU. -/
theorem rightShiftTensor_isMPU (d : ℕ) : IsMPU (rightShiftTensor d) := by
  intro N hN
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hN)⟩
  rw [mpo_rightShiftTensor]
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp

/-- The adjoint tensor generates the left shift. -/
def leftShiftTensor (d : ℕ) : MPOTensor d d :=
  physicalAdjointTensor (rightShiftTensor d)

/-- The adjoint shift has the expected all-chain operator formula. -/
theorem mpo_leftShiftTensor (d N : ℕ) [NeZero N] :
    mpo (leftShiftTensor d) N =
      (Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ := by
  rw [leftShiftTensor, mpo_physicalAdjointTensor_eq_conjTranspose,
    mpo_rightShiftTensor]

/-- The left-shift tensor is an MPU. -/
theorem leftShiftTensor_isMPU (d : ℕ) : IsMPU (leftShiftTensor d) :=
  (rightShiftTensor_isMPU d).physicalAdjointTensor

/-- The bond-one identity MPO tensor. -/
noncomputable def identityMPUTensor (d : ℕ) : MPOTensor d 1 := idTensor d

/-- The identity tensor generates the identity on every chain. -/
theorem mpo_identityMPUTensor (d N : ℕ) : mpo (identityMPUTensor d) N = 1 :=
  mpo_idTensor d N

/-- The identity tensor is an MPU. -/
theorem identityMPUTensor_isMPU (d : ℕ) : IsMPU (identityMPUTensor d) := by
  intro N _hN
  rw [mpo_identityMPUTensor, Matrix.mem_unitaryGroup_iff]
  simp

/-- The paper's `U₁`, the identity on two spins at each site. -/
noncomputable def shiftExampleU₁ (d : ℕ) : MPOTensor (d * d) 1 :=
  tensorProduct (identityMPUTensor d) (identityMPUTensor d)

/-- The paper's `U₂ = T† ⊗ T`. -/
def shiftExampleU₂ (d : ℕ) : MPOTensor (d * d) (d * d) :=
  tensorProduct (leftShiftTensor d) (rightShiftTensor d)

/-- The paper's `U₃ = T ⊗ T†`. -/
def shiftExampleU₃ (d : ℕ) : MPOTensor (d * d) (d * d) :=
  tensorProduct (rightShiftTensor d) (leftShiftTensor d)

/-- Exact all-chain formula for `U₁`. -/
theorem mpo_shiftExampleU₁ (d N : ℕ) : mpo (shiftExampleU₁ d) N = 1 := by
  rw [shiftExampleU₁, mpo_tensorProduct, mpo_identityMPUTensor,
    Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv _

/-- Exact all-chain formula for `U₂`. -/
theorem mpo_shiftExampleU₂ (d N : ℕ) [NeZero N] :
    mpo (shiftExampleU₂ d) N =
      Matrix.reindex (tensorProductConfigEquiv N d d).symm
        (tensorProductConfigEquiv N d d).symm
        ((Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ ⊗ₖ
          Equiv.Perm.permMatrix ℂ (rotateConfig N d)) := by
  rw [shiftExampleU₂, mpo_tensorProduct, mpo_leftShiftTensor,
    mpo_rightShiftTensor]

/-- Exact all-chain formula for `U₃`. -/
theorem mpo_shiftExampleU₃ (d N : ℕ) [NeZero N] :
    mpo (shiftExampleU₃ d) N =
      Matrix.reindex (tensorProductConfigEquiv N d d).symm
        (tensorProductConfigEquiv N d d).symm
        (Equiv.Perm.permMatrix ℂ (rotateConfig N d) ⊗ₖ
          (Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ) := by
  rw [shiftExampleU₃, mpo_tensorProduct, mpo_rightShiftTensor,
    mpo_leftShiftTensor]

/-- `U₁` is an MPU. -/
theorem shiftExampleU₁_isMPU (d : ℕ) : IsMPU (shiftExampleU₁ d) :=
  (identityMPUTensor_isMPU d).tensorProduct (identityMPUTensor_isMPU d)

/-- `U₂` is an MPU. -/
theorem shiftExampleU₂_isMPU (d : ℕ) : IsMPU (shiftExampleU₂ d) :=
  (leftShiftTensor_isMPU d).tensorProduct (rightShiftTensor_isMPU d)

/-- `U₃` is an MPU. -/
theorem shiftExampleU₃_isMPU (d : ℕ) : IsMPU (shiftExampleU₃ d) :=
  (rightShiftTensor_isMPU d).tensorProduct (leftShiftTensor_isMPU d)

end MPOTensor
