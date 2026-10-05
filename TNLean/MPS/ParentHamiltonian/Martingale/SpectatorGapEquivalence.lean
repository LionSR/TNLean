/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport

/-!
# Norm gaps with finite spectator coordinates

Extending an operator independently over a nonempty finite spectator space
preserves every nonnegative lower norm bound on its kernel complement. In
particular, replacing one nonempty finite spectator space by another preserves
the bound exactly, regardless of their dimensions. No positivity or symmetry
assumption on the operator is needed.

These results concern a common operator on the active coordinates. Identifying
a Hamiltonian with such a fiberwise extension remains a separate hypothesis.
-/

open scoped BigOperators InnerProductSpace

namespace ContinuousLinearMap

variable {I S T : Type*} [Fintype I] [Fintype S] [Fintype T]

/-- Orthogonality to the kernel of a fiberwise extension is equivalent to
orthogonality to the base kernel on every spectator fiber. -/
theorem mem_orthogonal_ker_rightFiberwiseMap_iff
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × S)) :
    x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ ↔
      ∀ s, rightFiber x s ∈ (LinearMap.ker G.toLinearMap)ᗮ := by
  have hProjection :
      (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap).starProjection x =
        rightFiberwiseMap (S := S) (LinearMap.ker G.toLinearMap).starProjection x :=
    LinearMap.congr_fun (ker_starProjection_rightFiberwiseMap (S := S) G) x
  rw [← Submodule.starProjection_apply_eq_zero_iff, hProjection]
  change x ∈ LinearMap.ker
    (rightFiberwiseMap (S := S) (LinearMap.ker G.toLinearMap).starProjection).toLinearMap ↔ _
  rw [mem_ker_rightFiberwiseMap_iff]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Submodule.starProjection_apply_eq_zero_iff]

/-- The squared norm is the sum of the squared norms of the spectator fibers. -/
theorem norm_sq_eq_sum_norm_sq_rightFiber (x : EuclideanSpace ℂ (I × S)) :
    ‖x‖ ^ 2 = ∑ s, ‖rightFiber x s‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [EuclideanSpace.norm_sq_eq]
  rfl

omit [Fintype I] [Fintype S] in
/-- Taking a fiber of a vector supported at one spectator coordinate gives
the original vector at that coordinate and zero elsewhere. -/
@[simp] theorem rightFiber_singleRightFiber [DecidableEq S]
    (s t : S) (x : EuclideanSpace ℂ I) :
    rightFiber (singleRightFiber s x) t = if t = s then x else 0 := by
  classical
  by_cases h : t = s <;> apply PiLp.ext <;> intro i <;>
    simp [rightFiber, singleRightFiber, h]

/-- A fiberwise operator preserves support on a single spectator coordinate. -/
@[simp] theorem rightFiberwiseMap_singleRightFiber
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (s : S) (x : EuclideanSpace ℂ I) :
    rightFiberwiseMap (S := S) G (singleRightFiber s x) = singleRightFiber s (G x) := by
  classical
  apply PiLp.ext
  rintro ⟨i, t⟩
  rw [rightFiberwiseMap_apply_apply, rightFiber_singleRightFiber]
  by_cases h : t = s <;> simp [singleRightFiber, h]

/-- A single-fiber vector is orthogonal to the extended kernel exactly when
its active vector is orthogonal to the original kernel. -/
theorem singleRightFiber_mem_orthogonal_ker_rightFiberwiseMap_iff
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (s : S) (x : EuclideanSpace ℂ I) :
    singleRightFiber s x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ ↔
      x ∈ (LinearMap.ker G.toLinearMap)ᗮ := by
  classical
  rw [mem_orthogonal_ker_rightFiberwiseMap_iff]
  constructor
  · intro h
    simpa using h s
  · intro h t
    by_cases ht : t = s
    · simpa [ht] using h
    · simp [ht]

/-- A lower norm bound on the kernel complement extends to all finite
spectator fibers with the same constant, even if the spectator type is empty. -/
theorem norm_gap_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ x ∈ (LinearMap.ker G.toLinearMap)ᗮ, δ * ‖x‖ ≤ ‖G x‖) :
    ∀ x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖rightFiberwiseMap (S := S) G x‖ := by
  intro x hx
  have hFiber := (mem_orthogonal_ker_rightFiberwiseMap_iff G x).mp hx
  apply (sq_le_sq₀ (mul_nonneg hδ (norm_nonneg _)) (norm_nonneg _)).mp
  calc
    (δ * ‖x‖) ^ 2 = ∑ s, (δ * ‖rightFiber x s‖) ^ 2 := by
      rw [mul_pow, norm_sq_eq_sum_norm_sq_rightFiber, Finset.mul_sum]
      simp only [mul_pow]
    _ ≤ ∑ s, ‖G (rightFiber x s)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      exact (sq_le_sq₀ (mul_nonneg hδ (norm_nonneg _)) (norm_nonneg _)).mpr
        (hGap _ (hFiber s))
    _ = ‖rightFiberwiseMap (S := S) G x‖ ^ 2 := by
      rw [norm_sq_eq_sum_norm_sq_rightFiber]
      simp only [rightFiber_rightFiberwiseMap]

/-- A nonempty finite spectator extension has exactly the same lower norm
bounds on the kernel complement as its active operator. -/
theorem norm_gap_rightFiberwiseMap_iff [Nonempty S]
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖rightFiberwiseMap (S := S) G x‖) ↔
      ∀ x ∈ (LinearMap.ker G.toLinearMap)ᗮ, δ * ‖x‖ ≤ ‖G x‖ := by
  constructor
  · intro hGap x hx
    let s : S := Classical.choice ‹Nonempty S›
    have hSingle :=
      (singleRightFiber_mem_orthogonal_ker_rightFiberwiseMap_iff G s x).mpr hx
    simpa only [rightFiberwiseMap_singleRightFiber, norm_singleRightFiber] using
      hGap (singleRightFiber s x) hSingle
  · exact norm_gap_rightFiberwiseMap G hδ

/-- Replacing a nonempty finite spectator space by any other nonempty finite
spectator space preserves a lower norm bound on the kernel complement exactly. -/
theorem norm_gap_rightFiberwiseMap_iff_rightFiberwiseMap [Nonempty S] [Nonempty T]
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖rightFiberwiseMap (S := S) G x‖) ↔
      ∀ x ∈ (LinearMap.ker (rightFiberwiseMap (S := T) G).toLinearMap)ᗮ,
        δ * ‖x‖ ≤ ‖rightFiberwiseMap (S := T) G x‖ :=
  (norm_gap_rightFiberwiseMap_iff (S := S) G hδ).trans
    (norm_gap_rightFiberwiseMap_iff (S := T) G hδ).symm

end ContinuousLinearMap
