/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# Stability of a norm gap when the kernel projection varies

A lower bound away from the kernel remains strict under small changes of
both the operator and its kernel projection. The norm estimate below is
used for the finite-window parent Hamiltonians in the gap argument of
arXiv:1010.3732, Appendix A.
-/

open scoped Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Perturbing an operator and its kernel projection preserves a lower norm
bound, with an explicit loss. The estimate uses only norms; the application
to parent Hamiltonians uses orthogonal kernel projections.
Source: arXiv:1010.3732, Appendix A, finite-window gap continuity. -/
theorem kernelGap_perturbation
    (H H₀ P P₀ : E →L[ℂ] E) {δ ε r : ℝ} (hδ : 0 ≤ δ)
    (hgap : ∀ v, δ * ‖v - P₀ v‖ ≤ ‖H₀ v‖)
    (hH : ‖H - H₀‖ ≤ ε) (hP : ‖P - P₀‖ ≤ r)
    (v : E) (hv : P v = 0) :
    (δ * (1 - r) - ε) * ‖v‖ ≤ ‖H v‖ := by
  have hPv : ‖P₀ v‖ ≤ r * ‖v‖ := by
    calc
      ‖P₀ v‖ = ‖(P - P₀) v‖ := by simp [hv]
      _ ≤ ‖P - P₀‖ * ‖v‖ := (P - P₀).le_opNorm v
      _ ≤ r * ‖v‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg v)
  have hHv : ‖H₀ v‖ ≤ ‖H v‖ + ε * ‖v‖ := by
    calc
      ‖H₀ v‖ ≤ ‖H v‖ + ‖(H - H₀) v‖ := by
        simpa only [sub_apply, norm_sub_rev] using
          norm_le_norm_add_norm_sub (H v) (H₀ v)
      _ ≤ ‖H v‖ + ε * ‖v‖ :=
        add_le_add (le_refl _) ((H - H₀).le_opNorm v |>.trans
          (mul_le_mul_of_nonneg_right hH (norm_nonneg v)))
  have hnorm : ‖v‖ ≤ ‖v - P₀ v‖ + r * ‖v‖ := by
    have ht := norm_le_norm_add_norm_sub (P₀ v) v
    rw [norm_sub_rev] at ht
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hnorm hδ, hgap v]

/-- A norm gap on the orthogonal complement of a subspace in the kernel
controls the component perpendicular to that subspace for every vector.
Source: arXiv:1010.3732, Appendix A, finite-window gap continuity. -/
theorem norm_gap_sub_starProjection
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (H : F →L[ℂ] F) (K : Submodule ℂ F) [K.HasOrthogonalProjection]
    (hker : K ≤ LinearMap.ker H.toLinearMap) {δ : ℝ}
    (hgap : ∀ v ∈ Kᗮ, δ * ‖v‖ ≤ ‖H v‖) (v : F) :
    δ * ‖v - K.starProjection v‖ ≤ ‖H v‖ := by
  have h := hgap _ (K.sub_starProjection_mem_orthogonal v)
  have hk : H (K.starProjection v) = 0 := hker (K.starProjection_apply_mem v)
  rw [map_sub, hk, sub_zero] at h
  exact h

/-- Any strictly smaller norm gap persists near a parameter where both the
operator and the chosen kernel projection vary continuously. The conclusion
applies to vectors annihilated by that projection. Source: arXiv:1010.3732,
Appendix A, finite-window gap continuity. -/
theorem eventually_kernelGap_of_continuousAt
    {X : Type*} [TopologicalSpace X] (H P : X → E →L[ℂ] E) {x₀ : X}
    (hH : ContinuousAt H x₀) (hP : ContinuousAt P x₀)
    {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : δ' < δ)
    (hgap : ∀ v, δ * ‖v - P x₀ v‖ ≤ ‖H x₀ v‖) :
    ∀ᶠ x in 𝓝 x₀, ∀ v, P x v = 0 → δ' * ‖v‖ ≤ ‖H x v‖ := by
  let ε := (δ - δ') / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hr : 0 < ε / δ := div_pos hε hδ
  filter_upwards [hH.eventually (eventually_norm_sub_lt (H x₀) hε),
    hP.eventually (eventually_norm_sub_lt (P x₀) hr)] with x hxH hxP
  intro v hv
  have h := kernelGap_perturbation (H x) (H x₀) (P x) (P x₀)
    hδ.le hgap hxH.le hxP.le v hv
  have heq : δ * (1 - ε / δ) - ε = δ' := by
    dsimp only [ε]
    field_simp
    ring
  simpa only [heq] using h

/-- A strict gap on an orthogonal complement persists when the operator and
the orthogonal projection vary continuously. At the base point the projected
subspace lies in the kernel. Source: arXiv:1010.3732, Appendix A. -/
theorem eventually_norm_gap_on_orthogonal
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {X : Type*} [TopologicalSpace X]
    (H : X → F →L[ℂ] F) (K : X → Submodule ℂ F)
    [∀ x, (K x).HasOrthogonalProjection] {x₀ : X}
    (hH : ContinuousAt H x₀)
    (hK : ContinuousAt (fun x => (K x).starProjection) x₀)
    (hker : K x₀ ≤ LinearMap.ker (H x₀).toLinearMap)
    {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : δ' < δ)
    (hgap : ∀ v ∈ (K x₀)ᗮ, δ * ‖v‖ ≤ ‖H x₀ v‖) :
    ∀ᶠ x in 𝓝 x₀, ∀ v ∈ (K x)ᗮ, δ' * ‖v‖ ≤ ‖H x v‖ := by
  have h := eventually_kernelGap_of_continuousAt H (fun x => (K x).starProjection)
    hH hK hδ hδ' (norm_gap_sub_starProjection (H x₀) (K x₀) hker hgap)
  filter_upwards [h] with x hx
  intro v hv
  apply hx v
  change v ∈ LinearMap.ker (K x).starProjection.toLinearMap
  simpa only [Submodule.ker_starProjection] using hv

end ContinuousLinearMap
