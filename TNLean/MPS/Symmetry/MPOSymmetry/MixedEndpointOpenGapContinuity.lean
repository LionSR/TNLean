/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenKernel
import TNLean.Algebra.CompactKernelGap

/-!
# Finite-window gap continuity for the actual mixed interaction

The open Hamiltonian and its exact extended kernel projection are continuous
through both endpoints. Consequently every strictly smaller fixed-window gap
persists in a parameter neighborhood. On a compact parameter set the gap is
uniform for that fixed window. The bound here may depend on the window length;
a strict Knabe window or a uniform many-body gap is a separate assertion.

Source: arXiv:2203.12563, Section 5, lines 1690–1692; the finite-window
perturbation argument is arXiv:1010.3732, Appendix A, lines 2575–2578.
-/

open scoped Topology

namespace MPSTensor

/-- Extension and cyclic placement preserve continuity of a local operator
family in operator norm. -/
theorem continuous_periodicLocalInteractionES_family
    {X : Type*} [TopologicalSpace X] {d R N : ℕ}
    (h : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hh : Continuous h) (i : Fin N) :
    Continuous fun x => (periodicLocalInteractionES (h x).toLinearMap i).toContinuousLinearMap := by
  by_cases hRN : R ≤ N
  · let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
    simp only [periodicLocalInteractionES, dite_eq_left hRN]
    apply continuous_clm_apply.2
    intro v
    have hfiber : Continuous fun x => ContinuousLinearMap.rightFiberwiseMap
        (S := Cfg d (N - R)) (h x) (U v) := by
      apply (EuclideanSpace.equiv (Cfg d R × Cfg d (N - R)) ℂ).symm.continuous.comp
      apply continuous_pi
      rintro ⟨ω, τ⟩
      exact (continuous_apply ω).comp
        ((EuclideanSpace.equiv (Cfg d R) ℂ).continuous.comp
          (hh.clm_apply (continuous_const : Continuous fun _ : X =>
            ContinuousLinearMap.rightFiber (U v) τ)))
    change Continuous fun x => U.symm
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R)) (h x) (U v))
    exact U.symm.continuous.comp hfiber
  · simp only [periodicLocalInteractionES, dite_eq_right hRN]
    exact continuous_const

/-- The nonwrapping sum of a continuous local interaction family is
continuous at every fixed volume. -/
theorem continuous_openInteractionHamiltonianES_family
    {X : Type*} [TopologicalSpace X] {d R : ℕ}
    (h : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hh : Continuous h) (N : ℕ) :
    Continuous fun x =>
      (openInteractionHamiltonianES (h x).toLinearMap N).toContinuousLinearMap := by
  have hsum : Continuous fun x => ∑ i : NonwrappingStart R N,
      (periodicLocalInteractionES (h x).toLinearMap i.1).toContinuousLinearMap :=
    continuous_finsetSum _ fun i _ => continuous_periodicLocalInteractionES_family h hh i.1
  convert hsum using 1
  funext x
  ext v
  simp [openInteractionHamiltonianES]

namespace MPOSymmetry

variable {D₀ D₁ N : ℕ}

/-- In the open parameter interval, the extended nonwrapping Hamiltonian
is exactly the canonical open parent of the actual interpolated tensor.
This permits using the canonical Knabe theorem after finite-window
continuity has produced a strict window estimate.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_openInteractionHamiltonianES_eq_of_mem_Ioo
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (N : ℕ) :
    openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N =
      openParentHamiltonianES (mixedEndpointInterpolation A₀ A₁ γ) 2 N := by
  rw [mixedEndpointParentInteraction_eq_parentInteractionES A₀ A₁ hγ]
  exact openInteractionHamiltonianES_parentInteractionES _ (by norm_num) N


/-- A strictly smaller gap of the actual fixed-window mixed open Hamiltonian
persists near every real parameter, including either endpoint. The exact
open kernel is used, so no kernel-continuity assumption is supplied.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem eventually_mixedEndpoint_open_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hN : 2 ≤ N)
    {γ₀ δ δ' : ℝ} (hδ : 0 < δ) (hδ' : δ' < δ)
    (hgap : ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ₀).toLinearMap N))ᗮ,
      δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ₀).toLinearMap N v‖) :
    ∀ᶠ γ in 𝓝 γ₀, ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
      δ' * ‖v‖ ≤ ‖openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖ := by
  exact ContinuousLinearMap.eventually_norm_gap_on_orthogonal
    (fun γ => (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N).toContinuousLinearMap)
    (fun γ => LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))
    (continuous_openInteractionHamiltonianES_family _
      (continuous_mixedEndpointParentInteraction A₀ A₁ h₀ h₁ hD₀ hD₁) N).continuousAt
    (continuous_mixedEndpoint_open_ker_starProjection A₀ A₁ h₀ h₁ hD₀ hD₁ hN).continuousAt
    le_rfl hδ hδ' hgap

/-- At each fixed open-chain length, the mixed interpolation has a positive
gap uniform over a compact set of parameters. The bound may depend on that
length; this theorem does not assert a uniform thermodynamic gap.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_uniform_mixedEndpoint_open_gap_fixed_volume
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hN : 2 ≤ N)
    {S : Set ℝ} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ ∈ S,
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖ :=
  ContinuousLinearMap.exists_uniform_norm_gap_of_compact
    (fun γ => (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N).toContinuousLinearMap)
    (continuous_openInteractionHamiltonianES_family _
      (continuous_mixedEndpointParentInteraction A₀ A₁ h₀ h₁ hD₀ hD₁) N)
    (continuous_mixedEndpoint_open_ker_starProjection A₀ A₁ h₀ h₁ hD₀ hD₁ hN) hS

end MPOSymmetry
end MPSTensor
