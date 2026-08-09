/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OperatorNormFrobenius
import TNLean.MPS.ParentHamiltonian.GroundSpaceGram
import TNLean.Spectral.QuantitativeGap

/-!
# Convergence of MPS ground-space Gram operators

This file bounds the ground-space Gram operator by combining the exact Choi
reshuffling identity with geometric decay of the complementary transfer map.
-/

open scoped Matrix Matrix.Norms.L2Operator NNReal ENNReal
open Matrix

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

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

end MPSTensor
