/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OperatorNormFrobenius
import TNLean.MPS.ParentHamiltonian.GroundSpaceGram
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.Spectral.TransferOperatorGapCommon

/-!
# Convergence of MPS ground-space Gram operators

This file bounds the ground-space Gram operator by combining the exact Choi
reshuffling identity with geometric decay of the complementary transfer map.

## Main results

- `MPSTensor.groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric`
- `MPSTensor.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj`
- `MPSTensor.IsPrimitiveMPS.groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric`
- `MPSTensor.IsPrimitiveMPS.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj`
-/

open scoped Matrix Matrix.Norms.L2Operator NNReal ENNReal
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- If the complementary transfer map has spectral radius less than one, then the
squared distance from the ground-space Gram operator to the reshuffled fixed-point
projection decays geometrically, up to the dimension-cubed norm-conversion factor. -/
theorem groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : trace ρ ≠ 0)
    (hTP : IsTracePreservingMap (transferMap A))
    (hρ : transferMap A ρ = ρ)
    (hgap :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (transferMap A - fixedPointProj ρ htr)) < 1) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ n, 1 ≤ n →
      ‖groundSpaceGram A n - Matrix.gramReshuffle (fixedPointProj ρ htr)‖ ^ 2 ≤
        (D : ℝ) ^ 3 * (C * r ^ n) ^ 2 := by
  let N := transferMap A - fixedPointProj ρ htr
  let T := (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) N
  rcases geometric_bound_of_spectralRadius_lt_one T (by simpa [T, N] using hgap) with
    ⟨C, r, hC, hr_pos, hr_lt_one, hbound⟩
  refine ⟨C, r, hC, hr_pos, hr_lt_one, ?_⟩
  intro n hn
  have hpow : (transferMap A) ^ n = fixedPointProj ρ htr + N ^ n := by
    simpa [N] using
      pow_eq_fixedPointProj_add_compl_pow (E := transferMap A) (ρ := ρ) htr hTP hρ hn
  calc
    ‖groundSpaceGram A n - Matrix.gramReshuffle (fixedPointProj ρ htr)‖ ^ 2 =
        ‖Matrix.gramReshuffle (N ^ n)‖ ^ 2 := by
      rw [groundSpaceGram_eq_gramReshuffle, ← Matrix.gramReshuffle_sub, hpow]
      simp
    _ ≤ (D : ℝ) ^ 3 *
        ‖LinearMap.toContinuousLinearMap (N ^ n)‖ ^ 2 := by
      simpa using Matrix.gramReshuffle_norm_sq_le_card_cube_mul_opNorm_sq (N ^ n)
    _ = (D : ℝ) ^ 3 * ‖T ^ n‖ ^ 2 := by
      change (D : ℝ) ^ 3 *
        ‖(Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (N ^ n)‖ ^ 2 = _
      rw [map_pow (Module.End.toContinuousLinearMap
        (Matrix (Fin D) (Fin D) ℂ)) N n]
    _ ≤ (D : ℝ) ^ 3 * (C * r ^ n) ^ 2 := by
      gcongr
      exact hbound n

/-- Under the same complementary spectral-radius hypothesis, the ground-space Gram
operators converge to the reshuffled fixed-point projection. -/
theorem groundSpaceGram_tendsto_gramReshuffle_fixedPointProj
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : trace ρ ≠ 0)
    (hTP : IsTracePreservingMap (transferMap A))
    (hρ : transferMap A ρ = ρ)
    (hgap :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (transferMap A - fixedPointProj ρ htr)) < 1) :
    Filter.Tendsto (fun n => groundSpaceGram A n) Filter.atTop
      (nhds (Matrix.gramReshuffle (fixedPointProj ρ htr))) := by
  rcases groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric
    A ρ htr hTP hρ hgap with ⟨C, r, _hC, hr_pos, hr_lt_one, hbound⟩
  have hrpow : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_pos.le hr_lt_one
  have hrhs : Filter.Tendsto
      (fun n : ℕ => (D : ℝ) ^ 3 * (C * r ^ n) ^ 2) Filter.atTop (nhds 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hrpow).pow 2))
  have hsq : Filter.Tendsto
      (fun n : ℕ =>
        ‖groundSpaceGram A n - Matrix.gramReshuffle (fixedPointProj ρ htr)‖ ^ 2)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      _ hrhs
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact hbound n hn
  have hnorm : Filter.Tendsto
      (fun n : ℕ =>
        ‖groundSpaceGram A n - Matrix.gramReshuffle (fixedPointProj ρ htr)‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    change Filter.Tendsto
      (fun n : ℕ =>
        Real.sqrt
          (‖groundSpaceGram A n - Matrix.gramReshuffle (fixedPointProj ρ htr)‖ ^ 2))
      Filter.atTop (nhds (Real.sqrt 0)) at hsqrt
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  exact hnorm

/-- A primitive MPS tensor satisfies the quantitative geometric bound for convergence of
its ground-space Gram operators to the reshuffled fixed-point projection. -/
theorem IsPrimitiveMPS.groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ n, 1 ≤ n →
      ‖groundSpaceGram A n - Matrix.gramReshuffle
        (fixedPointProj ρ (by
          intro h
          exact hP.fixedPoint_ne_zero
            ((Matrix.PosSemidef.trace_eq_zero_iff hP.fixedPoint_psd).1 h)))‖ ^ 2 ≤
        (D : ℝ) ^ 3 * (C * r ^ n) ^ 2 := by
  have htr : trace ρ ≠ 0 := by
    intro h
    exact hP.fixedPoint_ne_zero
      ((Matrix.PosSemidef.trace_eq_zero_iff hP.fixedPoint_psd).1 h)
  have hTP : IsTracePreservingMap (transferMap A) := by
    intro X
    exact trace_transferMap A X hP.norm
  exact MPSTensor.groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric
    A ρ htr hTP hP.fixedPoint_is_fixed hP.complementary_transfer_map_gap

/-- The ground-space Gram operators of a primitive MPS tensor converge to the reshuffled
fixed-point projection. -/
theorem IsPrimitiveMPS.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) :
    Filter.Tendsto (fun n => groundSpaceGram A n) Filter.atTop
      (nhds (Matrix.gramReshuffle
        (fixedPointProj ρ (by
          intro h
          exact hP.fixedPoint_ne_zero
            ((Matrix.PosSemidef.trace_eq_zero_iff hP.fixedPoint_psd).1 h))))) := by
  have htr : trace ρ ≠ 0 := by
    intro h
    exact hP.fixedPoint_ne_zero
      ((Matrix.PosSemidef.trace_eq_zero_iff hP.fixedPoint_psd).1 h)
  have hTP : IsTracePreservingMap (transferMap A) := by
    intro X
    exact trace_transferMap A X hP.norm
  exact MPSTensor.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj
    A ρ htr hTP hP.fixedPoint_is_fixed hP.complementary_transfer_map_gap

end MPSTensor
