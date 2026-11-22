/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointOpenKernel
import QICLean.Spectral.Gap.CompactKernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates

/-!
# Finite-window gap continuity for the actual mixed interaction

The open Hamiltonian and its exact extended kernel projection are continuous
through both endpoints. Consequently every strictly smaller fixed-window gap
persists in a parameter neighborhood. On a compact parameter set the gap is
uniform for that fixed window. The gaps are stated for the matrix of the open-chain
Hamiltonian: a nonzero kernel and a lower bound on the nonzero eigenvalues.
The bound here may depend on the window length;
a strict Knabe window or a uniform many-body gap is a separate assertion.

Source: arXiv:2203.12563, Section 5, lines 1690–1692; the finite-window
perturbation argument is arXiv:1010.3732, Appendix A, lines 2575–2578.
-/

open scoped Topology

namespace MPSTensor
namespace MPOSymmetry

open ManyBody.Interaction (chainTranslates)

variable {D₀ D₁ N : ℕ}

/-- In the open parameter interval, the open-chain Hamiltonian of the translates of the
extended interaction is exactly the canonical open parent Hamiltonian of the actual
interpolated tensor. This permits using the canonical Knabe theorem after finite-window
continuity has produced a strict window estimate.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_hamiltonian_chainTranslates_eq_of_mem_Ioo
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (N : ℕ) :
    (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian =
      (parentChainInteraction (mixedEndpointInterpolation A₀ A₁ γ) 2 N).hamiltonian := by
  rw [mixedEndpointParentInteraction_eq_toMatrix'_parentInteraction A₀ A₁ hγ]

/-- A strictly smaller gap of the fixed-window open-chain Hamiltonian of the translates of the
extended interaction persists near every real parameter, including either endpoint. The exact
open kernel is used, so no kernel-continuity assumption is supplied.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem eventually_isGapped_mixedEndpoint_hamiltonian_chainTranslates
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hN : 2 ≤ N)
    {γ₀ δ δ' : ℝ} (hδ' : δ' < δ)
    (hgap : ManyBody.IsGapped
      (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ γ₀)).hamiltonian 0 δ) :
    ∀ᶠ γ in 𝓝 γ₀, ManyBody.IsGapped
      (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian 0 δ' := by
  refine ManyBody.eventually_isGapped_zero
    (H := fun γ : ℝ => (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian)
    ((ManyBody.Interaction.continuous_hamiltonian_chainTranslates 2 N).comp
      (continuous_mixedEndpointParentInteraction A₀ A₁ h₀ h₁ hD₀ hD₁)).continuousAt
    (Filter.Eventually.of_forall fun γ =>
      ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates
        (posSemidef_mixedEndpointParentInteraction A₀ A₁ γ) N) ?_ hgap hδ'
  simp_rw [ManyBody.groundSpace_zero]
  exact (continuous_mixedEndpoint_open_ker_starProjection A₀ A₁ h₀ h₁ hD₀ hD₁ hN).continuousAt

/-- At each fixed open-chain length, the Hamiltonian of the translates of the extended
interaction is gapped at zero with one positive gap over a compact set of parameters. The bound
may depend on that length; this theorem does not assert a uniform thermodynamic gap.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_uniform_isGapped_mixedEndpoint_hamiltonian_chainTranslates_fixed_volume
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hN : 2 ≤ N)
    {S : Set ℝ} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ ∈ S, ManyBody.IsGapped
      (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian 0 δ := by
  obtain ⟨δ, hδ, hgap⟩ := hS.exists_uniform_forall_hasEigenvalue
    (H := fun γ : ℝ => (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ γ)).hamiltonian)
    ((ManyBody.Interaction.continuous_hamiltonian_chainTranslates 2 N).comp
      (continuous_mixedEndpointParentInteraction A₀ A₁ h₀ h₁ hD₀ hD₁))
    (fun γ => ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ γ) N)
    (by
      simp_rw [ManyBody.groundSpace_zero]
      exact continuous_mixedEndpoint_open_ker_starProjection A₀ A₁ h₀ h₁ hD₀ hD₁ hN)
  exact ⟨δ, hδ, fun γ hγ => ManyBody.isGapped_zero_iff.mpr
    ⟨groundSpace_mixedEndpoint_hamiltonian_chainTranslates_ne_bot A₀ A₁ h₀ h₁ hD₀ hD₁ γ hN,
      hgap γ hγ⟩⟩

end MPOSymmetry
end MPSTensor
