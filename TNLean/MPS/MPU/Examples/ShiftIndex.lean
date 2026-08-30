/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.ShiftSourceFactors
import TNLean.MPS.MPU.Examples.ShiftSourceRanks
import TNLean.MPS.MPU.SourceIndexValue

/-!
# Specified-tensor source-index values of the shift examples

This module computes the source-index value of the specified right-shift,
left-shift, identity, and three displayed shift-family tensors.

**Scope restriction (specified tensors):** arXiv:1703.09188, lines 2037--2041,
states values of the public blocking-independent MPU index. The results here
compute the same formulas only for the displayed tensors and do not prove
independence of a chosen simple blocking. This restriction and its elimination
plan are recorded in
`docs/paper-gaps/mpu_shift_specified_tensor_index_scope.tex`.

Source: arXiv:1703.09188, lines 2037--2041.
-/

namespace MPOTensor

private theorem sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
    (U : MPOTensor d D) (hr : 0 < r[U]) (hℓ : 0 < ℓ[U])
    (h : r[U] = ℓ[U]) :
    sourceIndexValue U hr hℓ = 0 := by
  simp only [sourceIndexValue, h, sub_self, mul_zero]

/-- The source ranks of the specified right-shift tensor are positive. -/
lemma sourceRanks_pos_rightShiftTensor (d : ℕ) [NeZero d] :
    0 < r[rightShiftTensor d] ∧ 0 < ℓ[rightShiftTensor d] := by
  rw [rightRank_rightShiftTensor, leftRank_rightShiftTensor]
  exact ⟨Nat.mul_pos (NeZero.pos d) (NeZero.pos d), Nat.zero_lt_one⟩

/-- The source ranks of the specified left-shift tensor are positive. -/
lemma sourceRanks_pos_leftShiftTensor (d : ℕ) [NeZero d] :
    0 < r[leftShiftTensor d] ∧ 0 < ℓ[leftShiftTensor d] := by
  rw [rightRank_leftShiftTensor, leftRank_leftShiftTensor]
  exact ⟨Nat.zero_lt_one, Nat.mul_pos (NeZero.pos d) (NeZero.pos d)⟩

/-- The source ranks of the specified bond-one identity tensor are positive. -/
lemma sourceRanks_pos_identityMPUTensor (d : ℕ) [NeZero d] :
    0 < r[identityMPUTensor d] ∧ 0 < ℓ[identityMPUTensor d] := by
  rw [rightRank_identityMPUTensor, leftRank_identityMPUTensor]
  exact ⟨NeZero.pos d, NeZero.pos d⟩

/-- The source ranks of the specified tensor for $U_1$ are positive. -/
lemma sourceRanks_pos_shiftExampleU₁ (d : ℕ) [NeZero d] :
    0 < r[shiftExampleU₁ d] ∧ 0 < ℓ[shiftExampleU₁ d] := by
  simp only [shiftExampleU₁, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_identityMPUTensor, leftRank_identityMPUTensor]
  exact ⟨Nat.mul_pos (NeZero.pos d) (NeZero.pos d),
    Nat.mul_pos (NeZero.pos d) (NeZero.pos d)⟩

/-- The source ranks of the specified tensor for $U_2$ are positive. -/
lemma sourceRanks_pos_shiftExampleU₂ (d : ℕ) [NeZero d] :
    0 < r[shiftExampleU₂ d] ∧ 0 < ℓ[shiftExampleU₂ d] := by
  simp only [shiftExampleU₂, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_leftShiftTensor, rightRank_rightShiftTensor,
    leftRank_leftShiftTensor, leftRank_rightShiftTensor, one_mul, mul_one]
  exact ⟨Nat.mul_pos (NeZero.pos d) (NeZero.pos d),
    Nat.mul_pos (NeZero.pos d) (NeZero.pos d)⟩

/-- The source ranks of the specified tensor for $U_3$ are positive. -/
lemma sourceRanks_pos_shiftExampleU₃ (d : ℕ) [NeZero d] :
    0 < r[shiftExampleU₃ d] ∧ 0 < ℓ[shiftExampleU₃ d] := by
  simp only [shiftExampleU₃, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_rightShiftTensor, rightRank_leftShiftTensor,
    leftRank_rightShiftTensor, leftRank_leftShiftTensor, one_mul, mul_one]
  exact ⟨Nat.mul_pos (NeZero.pos d) (NeZero.pos d),
    Nat.mul_pos (NeZero.pos d) (NeZero.pos d)⟩

/-- The specified right-shift tensor has source-index value $\log_2 d$.

Source: arXiv:1703.09188, lines 2039--2041. This is a value for the displayed
tensor, not the blocking-independent MPU index. -/
theorem sourceIndexValue_rightShiftTensor (d : ℕ) [NeZero d] :
    sourceIndexValue (rightShiftTensor d)
      (sourceRanks_pos_rightShiftTensor d).1 (sourceRanks_pos_rightShiftTensor d).2 =
        Real.logb 2 d := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [sourceIndexValue, rightRank_rightShiftTensor, leftRank_rightShiftTensor,
    Nat.cast_mul, Real.logb_mul hd hd]
  norm_num
  ring

/-- The specified left-shift tensor has source-index value $-\log_2 d$.

Source: arXiv:1703.09188, lines 2039--2041. This is a value for the displayed
tensor, not the blocking-independent MPU index. -/
theorem sourceIndexValue_leftShiftTensor (d : ℕ) [NeZero d] :
    sourceIndexValue (leftShiftTensor d)
      (sourceRanks_pos_leftShiftTensor d).1 (sourceRanks_pos_leftShiftTensor d).2 =
        -Real.logb 2 d := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [sourceIndexValue, rightRank_leftShiftTensor, leftRank_leftShiftTensor,
    Nat.cast_mul, Real.logb_mul hd hd]
  norm_num
  ring

/-- The specified bond-one identity tensor has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2039. -/
theorem sourceIndexValue_identityMPUTensor (d : ℕ) [NeZero d] :
    sourceIndexValue (identityMPUTensor d)
      (sourceRanks_pos_identityMPUTensor d).1 (sourceRanks_pos_identityMPUTensor d).2 = 0 := by
  apply sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
  rw [rightRank_identityMPUTensor, leftRank_identityMPUTensor]

/-- The specified tensor for the identity family $U_1$ has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2039. -/
theorem sourceIndexValue_shiftExampleU₁ (d : ℕ) [NeZero d] :
    sourceIndexValue (shiftExampleU₁ d)
      (sourceRanks_pos_shiftExampleU₁ d).1 (sourceRanks_pos_shiftExampleU₁ d).2 = 0 := by
  apply sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
  simp only [shiftExampleU₁, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_identityMPUTensor, leftRank_identityMPUTensor]

/-- The specified tensor for the balanced shift family $U_2$ has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2039. -/
theorem sourceIndexValue_shiftExampleU₂ (d : ℕ) [NeZero d] :
    sourceIndexValue (shiftExampleU₂ d)
      (sourceRanks_pos_shiftExampleU₂ d).1 (sourceRanks_pos_shiftExampleU₂ d).2 = 0 := by
  apply sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
  simp only [shiftExampleU₂, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_leftShiftTensor, rightRank_rightShiftTensor,
    leftRank_leftShiftTensor, leftRank_rightShiftTensor, one_mul, mul_one]

/-- The specified tensor for the balanced shift family $U_3$ has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2039. -/
theorem sourceIndexValue_shiftExampleU₃ (d : ℕ) [NeZero d] :
    sourceIndexValue (shiftExampleU₃ d)
      (sourceRanks_pos_shiftExampleU₃ d).1 (sourceRanks_pos_shiftExampleU₃ d).2 = 0 := by
  apply sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
  simp only [shiftExampleU₃, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_rightShiftTensor, rightRank_leftShiftTensor,
    leftRank_rightShiftTensor, leftRank_leftShiftTensor, one_mul, mul_one]

end MPOTensor
