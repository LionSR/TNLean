/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.MPU.Examples.ShiftBlockedIndex
import TNLean.MPS.MPU.RepresentativeIndexOperations
import TNLean.MPS.MPU.RepresentativeIndexTensorProduct
import TNLean.MPS.MPU.Examples.ShiftPaperSourceFactors
import TNLean.MPS.MPU.TransferMatrix
import TNLean.MPS.MPU.TransferStabilizationConverse
import TNLean.MPS.SharedInfra.Scaling

/-!
# Public indices of the shift examples

The normalized right-shift transfer map is `X ↦ trace X • (I/d)`. This gives a
canonical-form-II representative, identifying the existing source-rank value
with the public index. Adjoint negation and tensor-product additivity then give
the left-shift value and the three zero-index examples.

Source: arXiv:1703.09188, `threeMPU` and lines 2037–2041.
This resolves `docs/paper-gaps/mpu_shift_specified_tensor_index_scope.tex`.
-/

open scoped Matrix

namespace MPOTensor

private theorem transferMap_rightShiftTensor (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) :
    Kraus.transferMap (rightShiftTensor d).toMPSTensor X = X.trace • 1 := by
  rw [Kraus.transferMap_apply, ← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, toMPSTensor, rightShiftTensor,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat, Matrix.conjTranspose_single,
    star_one, Matrix.single_mul_mul_single, one_mul, mul_one]
  ext i j
  simp [Matrix.sum_apply, Matrix.single, Matrix.trace, Matrix.smul_apply,
    Matrix.one_apply, ite_and]

private theorem transferMap_normalized_rightShiftTensor (d : ℕ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    Kraus.transferMap (rightShiftTensor d).normalizedFlattening X =
      X.trace • shiftPaperWeight d := by
  change Kraus.transferMap
    (fun i => (Real.sqrt d : ℂ)⁻¹ • (rightShiftTensor d).toMPSTensor i) X = _
  rw [MPSTensor.transferMap_smul, transferMap_rightShiftTensor]
  simp only [map_inv₀, Complex.conj_ofReal, smul_smul, shiftPaperWeight]
  simp [Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg d), mul_comm]

private theorem transferMatrix_normalized_rightShiftTensor (d : ℕ) :
    transferMatrix (Kraus.transferMap (rightShiftTensor d).normalizedFlattening) =
      Matrix.vecMulVec (shiftPaperWeight d).vec (1 : Matrix (Fin d) (Fin d) ℂ).vec := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [transferMatrix_apply, transferMap_normalized_rightShiftTensor]
  simp [Matrix.vecMulVec_apply, Matrix.vec, Matrix.trace, Matrix.single,
    Matrix.smul_apply, Matrix.one_apply, ite_and, mul_comm, eq_comm]

/-- The right shift has canonical-form-II data with trace-one fixed matrix `I/d`.
Source: CPSV17, equations `Erightleft` and `threeMPU`, lines 269–281 and 1980–2001. -/
theorem rightShiftTensor_exists_canonicalFormII (d : ℕ) [NeZero d] :
    ∃ h : IsMPUCanonicalFormII (rightShiftTensor d), h.ρ = shiftPaperWeight d := by
  apply (rightShiftTensor_isMPU d).exists_canonicalFormII_of_supplied_transfer_power
    (shiftPaperWeight d) (shiftPaperWeight_posDef d) (Matrix.isDiag_smul_one _ _) 1
  simpa only [pow_one] using transferMatrix_normalized_rightShiftTensor d

private theorem canonical_index_rightShiftTensor (d : ℕ) [NeZero d]
    (h : IsMPUCanonicalFormII (rightShiftTensor d)) : h.index = Real.logb 2 d := by
  exact (h.sourceIndexValue_eq_index (by decide : 0 < 0 + 1)
    (blockTensor_rightShiftTensor_isMPUSimple d 0)
    (sourceRanks_pos_blockTensor_rightShiftTensor (d := d) 0).1
    (sourceRanks_pos_blockTensor_rightShiftTensor (d := d) 0).2).symm.trans
      (sourceIndexValue_blockTensor_rightShiftTensor (d := d) 0)

/-- The right shift has public index `log₂ d` (CPSV17, lines 2037–2041). -/
theorem rightShiftTensor_index (d : ℕ) [NeZero d] :
    (rightShiftTensor_isMPU d).index = Real.logb 2 d := by
  obtain ⟨h, _⟩ := rightShiftTensor_exists_canonicalFormII d
  rw [(rightShiftTensor_isMPU d).index_eq_canonical_representative h (by intro N hN; rfl)]
  exact canonical_index_rightShiftTensor d h

/-- The left shift has public index `-log₂ d` (CPSV17, lines 2037–2041). -/
theorem leftShiftTensor_index (d : ℕ) [NeZero d] :
    (leftShiftTensor_isMPU d).index = -Real.logb 2 d := by
  simpa only [leftShiftTensor, rightShiftTensor_index] using
    (rightShiftTensor_isMPU d).index_physicalAdjointTensor

/-- The first two-spin example has public index zero (CPSV17, `threeMPU`, line 2037). -/
theorem shiftExampleU₁_index (d : ℕ) [NeZero d] :
    (shiftExampleU₁_isMPU d).index = 0 := by
  simpa only [shiftExampleU₁, IsMPU.index_identityMPUTensor, add_zero] using
    (identityMPUTensor_isMPU d).index_tensorProduct (identityMPUTensor_isMPU d)

/-- Oppositely directed shifts have public index zero (CPSV17, `threeMPU`, line 2037). -/
theorem shiftExampleU₂_index (d : ℕ) [NeZero d] :
    (shiftExampleU₂_isMPU d).index = 0 := by
  simpa only [shiftExampleU₂, leftShiftTensor_index, rightShiftTensor_index, neg_add_cancel] using
    (leftShiftTensor_isMPU d).index_tensorProduct (rightShiftTensor_isMPU d)

/-- Reversing the two shift factors preserves index zero (CPSV17, `threeMPU`, line 2037). -/
theorem shiftExampleU₃_index (d : ℕ) [NeZero d] :
    (shiftExampleU₃_isMPU d).index = 0 := by
  simpa only [shiftExampleU₃, leftShiftTensor_index, rightShiftTensor_index, add_neg_cancel] using
    (rightShiftTensor_isMPU d).index_tensorProduct (leftShiftTensor_isMPU d)

end MPOTensor
