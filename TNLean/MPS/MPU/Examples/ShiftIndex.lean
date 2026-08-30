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
left-shift, identity, and three displayed shift-family tensors. These results do
not assert that the value is independent of a choice of simple blocking.

Source: arXiv:1703.09188, lines 2037--2041.
-/

namespace MPOTensor

private theorem sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
    (U : MPOTensor d D) (hr : 0 < r[U]) (hℓ : 0 < ℓ[U])
    (h : r[U] = ℓ[U]) :
    sourceIndexValue U hr hℓ = 0 := by
  simp [sourceIndexValue, h]

/-- The specified right-shift tensor has source-index value $\log_2 d$.

Source: arXiv:1703.09188, lines 2039--2041. This is a value for the displayed
tensor, not the blocking-independent MPU index. -/
theorem sourceIndexValue_rightShiftTensor (d : ℕ) [NeZero d]
    (hr : 0 < r[rightShiftTensor d]) (hℓ : 0 < ℓ[rightShiftTensor d]) :
    sourceIndexValue (rightShiftTensor d) hr hℓ = Real.logb 2 d := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [sourceIndexValue, rightRank_rightShiftTensor, leftRank_rightShiftTensor,
    Nat.cast_mul, Real.logb_mul hd hd]
  norm_num
  ring

/-- The specified left-shift tensor has source-index value $-\log_2 d$.

Source: arXiv:1703.09188, lines 2039--2041. This is a value for the displayed
tensor, not the blocking-independent MPU index. -/
theorem sourceIndexValue_leftShiftTensor (d : ℕ) [NeZero d]
    (hr : 0 < r[leftShiftTensor d]) (hℓ : 0 < ℓ[leftShiftTensor d]) :
    sourceIndexValue (leftShiftTensor d) hr hℓ = -Real.logb 2 d := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [sourceIndexValue, rightRank_leftShiftTensor, leftRank_leftShiftTensor,
    Nat.cast_mul, Real.logb_mul hd hd]
  norm_num
  ring

/-- The specified bond-one identity tensor has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2039. -/
theorem sourceIndexValue_identityMPUTensor (d : ℕ) [NeZero d]
    (hr : 0 < r[identityMPUTensor d]) (hℓ : 0 < ℓ[identityMPUTensor d]) :
    sourceIndexValue (identityMPUTensor d) hr hℓ = 0 := by
  apply sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
  rw [rightRank_identityMPUTensor, leftRank_identityMPUTensor]

/-- The specified tensor for the identity family $U_1$ has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2039. -/
theorem sourceIndexValue_shiftExampleU₁ (d : ℕ) [NeZero d]
    (hr : 0 < r[shiftExampleU₁ d]) (hℓ : 0 < ℓ[shiftExampleU₁ d]) :
    sourceIndexValue (shiftExampleU₁ d) hr hℓ = 0 := by
  apply sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
  simp only [shiftExampleU₁, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_identityMPUTensor, leftRank_identityMPUTensor]

/-- The specified tensor for the balanced shift family $U_2$ has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2039. -/
theorem sourceIndexValue_shiftExampleU₂ (d : ℕ) [NeZero d]
    (hr : 0 < r[shiftExampleU₂ d]) (hℓ : 0 < ℓ[shiftExampleU₂ d]) :
    sourceIndexValue (shiftExampleU₂ d) hr hℓ = 0 := by
  apply sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
  simp only [shiftExampleU₂, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_leftShiftTensor, rightRank_rightShiftTensor,
    leftRank_leftShiftTensor, leftRank_rightShiftTensor, one_mul, mul_one]

/-- The specified tensor for the balanced shift family $U_3$ has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2039. -/
theorem sourceIndexValue_shiftExampleU₃ (d : ℕ) [NeZero d]
    (hr : 0 < r[shiftExampleU₃ d]) (hℓ : 0 < ℓ[shiftExampleU₃ d]) :
    sourceIndexValue (shiftExampleU₃ d) hr hℓ = 0 := by
  apply sourceIndexValue_eq_zero_of_rightRank_eq_leftRank
  simp only [shiftExampleU₃, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_rightShiftTensor, rightRank_leftShiftTensor,
    leftRank_rightShiftTensor, leftRank_leftShiftTensor, one_mul, mul_one]

end MPOTensor
