/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PositiveGapTransfer
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Spectral gaps under bounded invertible congruences

Let \(P\) be positive with gap \(\delta\) above its kernel, and let
\(e\) be an invertible linear map satisfying
\(\lVert e^{-1}w\rVert \le C\lVert w\rVert\).
Then \(e^*Pe\) is positive, its kernel is \(e^{-1}(\ker P)\), and
its gap is at least \(\delta/C^2\).

The constant depends only on the inverse bound. In particular, a deformation
supported on a bounded number of boundary sites can use this estimate once
its inverse bound has been established independently of the chain length.
No identification with a mixed-chain Hamiltonian is assumed or asserted here.
-/

open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Invertible congruence pulls back the kernel, without requiring positivity. -/
theorem LinearEquiv.ker_adjoint_congruence (e : E ≃ₗ[ℂ] F) (P : F →ₗ[ℂ] F) :
    LinearMap.ker (e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap) =
      (LinearMap.ker P).comap e.toLinearMap := by
  ext v
  change e.toLinearMap.adjoint (P (e v)) = 0 ↔ P (e v) = 0
  constructor
  · intro hv
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    calc
      ⟪P (e v), P (e v)⟫_ℂ =
          ⟪e.toLinearMap.adjoint (P (e v)), e.symm (P (e v))⟫_ℂ := by
        rw [LinearMap.adjoint_inner_left]
        simp
      _ = 0 := by rw [hv, inner_zero_left]
  · intro hv
    simp [hv]

namespace LinearMap.IsPositive

/-- A bounded inverse loses at most a factor \(C^2\) in a positive
operator's norm gap under congruence. The kernel in the conclusion is the
actual kernel of \(e^*Pe\). -/
theorem norm_gap_adjoint_congruence_of_inverse_bound
    {P : F →ₗ[ℂ] F} (hP : P.IsPositive) (e : E ≃ₗ[ℂ] F)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 < C)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖)
    (hGap : ∀ w ∈ (LinearMap.ker P)ᗮ, δ * ‖w‖ ≤ ‖P w‖) :
    ∀ v ∈ (LinearMap.ker (e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap))ᗮ,
      (δ / C ^ 2) * ‖v‖ ≤ ‖(e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap) v‖ := by
  intro v hv
  let Q := e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap
  let w := (LinearMap.ker P)ᗮ.starProjection (e v)
  let u := e.symm ((LinearMap.ker P).starProjection (e v))
  have hproj : P ((LinearMap.ker P).starProjection (e v)) = 0 :=
    LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem _ _)
  have hu : u ∈ LinearMap.ker Q := by
    rw [show LinearMap.ker Q = (LinearMap.ker P).comap e.toLinearMap from
      e.ker_adjoint_congruence P]
    change P (e u) = 0
    simpa only [u, e.apply_symm_apply] using hproj
  have horth : ⟪v, u⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hu hv
  have hdecomp : e.symm w = v - u := by
    simp only [w, u, Submodule.starProjection_orthogonal_val, map_sub,
      e.symm_apply_apply]
  have hnorm : ‖v‖ ≤ C * ‖w‖ := calc
    ‖v‖ ≤ ‖v - u‖ := by
      have hsq : ‖v - u‖ ^ 2 = ‖v‖ ^ 2 + ‖u‖ ^ 2 := by
        simpa only [horth, RCLike.zero_re, mul_zero, sub_zero] using
          norm_sub_sq (𝕜 := ℂ) v u
      nlinarith [norm_nonneg (v - u), norm_nonneg v, sq_nonneg ‖u‖]
    _ = ‖e.symm w‖ := congrArg norm hdecomp.symm
    _ ≤ C * ‖w‖ := hInverse w
  have hnormSq : ‖v‖ ^ 2 ≤ C ^ 2 * ‖w‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg v) hnorm 2
  have henergy : (⟪Q v, v⟫_ℂ).re = (⟪P w, w⟫_ℂ).re := by
    change (⟪e.toLinearMap.adjoint (P (e v)), v⟫_ℂ).re = _
    rw [LinearMap.adjoint_inner_left]
    change (⟪P (e v), e v⟫_ℂ).re = (⟪P w, w⟫_ℂ).re
    simp only [w, Submodule.starProjection_orthogonal_val, map_sub, hproj,
      sub_zero, hP.isSymmetric (e v)]
  have hquadratic : (δ / C ^ 2) * ‖v‖ ^ 2 ≤ ‖Q v‖ * ‖v‖ := calc
    (δ / C ^ 2) * ‖v‖ ^ 2 ≤ (δ / C ^ 2) * (C ^ 2 * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnormSq (by positivity)
    _ = δ * ‖w‖ ^ 2 := by field_simp [ne_of_gt hC]
    _ ≤ (⟪P w, w⟫_ℂ).re := hP.re_inner_ge_of_norm_gap hδ hGap w
      (Submodule.starProjection_apply_mem _ _)
    _ = (⟪Q v, v⟫_ℂ).re := henergy.symm
    _ ≤ ‖Q v‖ * ‖v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
  by_cases hv0 : v = 0
  · simp [hv0]
  · exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv0)).mp
      (by simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hquadratic)

/-- Positivity, the exact kernel, and the explicit positive gap of an
invertible congruence follow from the original gap and an inverse bound. -/
theorem bounded_congruence_gap {P : F →ₗ[ℂ] F} (hP : P.IsPositive)
    (e : E ≃ₗ[ℂ] F) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖)
    (hGap : ∀ w ∈ (LinearMap.ker P)ᗮ, δ * ‖w‖ ≤ ‖P w‖) :
    0 < δ / C ^ 2 ∧
      (e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap).IsPositive ∧
      LinearMap.ker (e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap) =
        (LinearMap.ker P).comap e.toLinearMap ∧
      ∀ v ∈ (LinearMap.ker (e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap))ᗮ,
        (δ / C ^ 2) * ‖v‖ ≤
          ‖(e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap) v‖ :=
  ⟨by positivity, hP.adjoint_conj e.toLinearMap, e.ker_adjoint_congruence P,
    hP.norm_gap_adjoint_congruence_of_inverse_bound e hδ.le hC hInverse hGap⟩

end LinearMap.IsPositive
