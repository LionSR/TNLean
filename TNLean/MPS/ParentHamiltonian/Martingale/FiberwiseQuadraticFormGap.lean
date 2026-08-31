/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.QuadraticFormGap
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport

/-!
# Fiberwise lifting of quadratic-form gaps

A quadratic-form inequality for an operator on an active finite configuration
space remains true when the operator acts independently over a finite right
spectator coordinate.
-/

open scoped BigOperators InnerProductSpace

namespace ContinuousLinearMap

variable {I S : Type*} [Fintype I] [Fintype S]

/-- The inequality \(G^2 \geq \gamma G\) is preserved when \(G\) is applied
independently on every right-spectator fiber. -/
theorem quadraticForm_sq_ge_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) {γ : ℝ}
    (hG : ∀ u,
      γ * (⟪G u, u⟫_ℂ).re ≤ (⟪G u, G u⟫_ℂ).re)
    (v : EuclideanSpace ℂ (I × S)) :
    γ * (⟪rightFiberwiseMap (S := S) G v, v⟫_ℂ).re ≤
      (⟪rightFiberwiseMap (S := S) G v,
        rightFiberwiseMap (S := S) G v⟫_ℂ).re := by
  classical
  have hleft : (⟪rightFiberwiseMap (S := S) G v, v⟫_ℂ).re =
      ∑ s : S, (⟪G (rightFiber v s), rightFiber v s⟫_ℂ).re := by
    rw [PiLp.inner_apply, Complex.re_sum, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [PiLp.inner_apply, Complex.re_sum]
    rfl
  have hright :
      (⟪rightFiberwiseMap (S := S) G v,
        rightFiberwiseMap (S := S) G v⟫_ℂ).re =
      ∑ s : S, (⟪G (rightFiber v s), G (rightFiber v s)⟫_ℂ).re := by
    rw [PiLp.inner_apply, Complex.re_sum, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [PiLp.inner_apply, Complex.re_sum]
    rfl
  rw [hleft, hright, Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ ↦ hG (rightFiber v s)

end ContinuousLinearMap

namespace LinearMap.IsPositive

variable {I S : Type*} [Fintype I] [Fintype S]

/-- A norm gap for a positive active operator supplies the global quadratic-form
inequality for its independent right-spectator extension. -/
theorem quadraticForm_sq_ge_rightFiberwiseMap_of_norm_gap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsPositive) {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ u ∈ (LinearMap.ker G.toLinearMap)ᗮ,
      γ * ‖u‖ ≤ ‖G u‖) :
    ∀ v : EuclideanSpace ℂ (I × S),
      γ * (⟪ContinuousLinearMap.rightFiberwiseMap (S := S) G v, v⟫_ℂ).re ≤
        (⟪ContinuousLinearMap.rightFiberwiseMap (S := S) G v,
          ContinuousLinearMap.rightFiberwiseMap (S := S) G v⟫_ℂ).re :=
  ContinuousLinearMap.quadraticForm_sq_ge_rightFiberwiseMap G
    (hG.quadraticForm_sq_ge_of_norm_gap hγ hGap)

end LinearMap.IsPositive
