/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PositiveGapTransfer

/-!
# Norm gaps as quadratic-form inequalities

This file records the finite-dimensional positive-operator estimate used to
supply the local quadratic-form hypothesis in the finite-range Knabe argument.
A norm gap of a positive operator on the orthogonal complement of its kernel
implies the global inequality \(H^2 \geq \gamma H\).
-/

open scoped InnerProductSpace

namespace LinearMap.IsPositive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- If a positive operator has norm gap \(\gamma\) on the orthogonal complement
of its kernel, then it satisfies \(H^2 \geq \gamma H\) as a quadratic form on
the whole space. -/
theorem quadraticForm_sq_ge_of_norm_gap {H : E →ₗ[ℂ] E} (hH : H.IsPositive)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ u ∈ (LinearMap.ker H)ᗮ, γ * ‖u‖ ≤ ‖H u‖) :
    ∀ v : E,
      γ * (⟪H v, v⟫_ℂ).re ≤ (⟪H v, H v⟫_ℂ).re := by
  classical
  intro v
  let w := v - (LinearMap.ker H).starProjection v
  have hw : w ∈ (LinearMap.ker H)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal v
  have hproj : H ((LinearMap.ker H).starProjection v) = 0 := by
    rw [← LinearMap.mem_ker]
    exact Submodule.starProjection_apply_mem _ _
  have hHw : H w = H v := by
    simp [w, hproj]
  have hcross : ⟪H v, (LinearMap.ker H).starProjection v⟫_ℂ = 0 := by
    rw [hH.isSymmetric v, hproj, inner_zero_right]
  have hinner : ⟪H v, v⟫_ℂ = ⟪H v, w⟫_ℂ := by
    calc
      ⟪H v, v⟫_ℂ = ⟪H v, w + (LinearMap.ker H).starProjection v⟫_ℂ := by
        congr 1
        simp [w]
      _ = ⟪H v, w⟫_ℂ := by rw [inner_add_right, hcross, add_zero]
  calc
    γ * (⟪H v, v⟫_ℂ).re = γ * (⟪H v, w⟫_ℂ).re := by rw [hinner]
    _ ≤ γ * (‖H v‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left (re_inner_le_norm (𝕜 := ℂ) (H v) w) hγ
    _ = ‖H v‖ * (γ * ‖w‖) := by ring
    _ ≤ ‖H v‖ * ‖H w‖ :=
      mul_le_mul_of_nonneg_left (hGap w hw) (norm_nonneg _)
    _ = (⟪H v, H v⟫_ℂ).re := by
      rw [hHw, ← pow_two]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (H v)).symm

end LinearMap.IsPositive
