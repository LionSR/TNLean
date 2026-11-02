/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalEndpointAttachment

/-!
# Ground projections of the arbitrary-alphabet mixed path

For each periodic length at least two, the orthogonal projection onto the
ground space of the enlarged mixed Hamiltonian depends continuously on the
parameter in the closed unit interval. At each endpoint it equals the
ground projection of the canonical parent Hamiltonian of the fully embedded
original tensor. Hence the ground projections converge to the canonical
endpoint projections as the parameter tends to an endpoint, and they stay
equal to them along the affine attachments to the canonical parents.

GLM23 obtains the endpoint limit through a Gram–Schmidt argument on the
extended supports, and states that the limiting Hamiltonian is gapped with
the endpoint state as unique ground state. Here the limit is identified with
the canonical parent projection itself; no limiting state, kernel
continuity, or gap is assumed.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, Section 5,
`REsubmission.tex`, lines 1690–1692, and the parent-Hamiltonian restriction,
lines 1328–1331.
-/

open scoped Matrix Topology

open Filter

namespace MPSTensor
namespace MPOSymmetry

variable {d₀ d₁ D₀ D₁ N : ℕ}

/-- The periodic ground space of the enlarged mixed Hamiltonian is the range
of the scalar-to-state map of the enlarged mixed tensor, on the whole closed
interval. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem arbitraryPhysicalMixedInteraction_groundSpace_eq_range
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN)) =
      (periodicMpvLineMap (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) N).range := by
  rw [arbitraryPhysicalMixedInteraction_groundSpace_eq_span_mpv A₀ A₁ h₀ h₁ γ hN]
  exact (ContinuousLinearMap.range_smulRight_apply
    (by norm_num : (1 : ℂ →L[ℂ] ℂ) ≠ 0) _).symm

/-- For each periodic length at least two, the ground projection of the
enlarged mixed Hamiltonian is continuous on the closed interval, including
both rank-changing endpoints. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem continuous_arbitraryPhysicalMixed_groundSpace_starProjection
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) (hN : 2 ≤ N) :
    Continuous fun γ : unitInterval =>
      (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN))).starProjection := by
  have hT := continuous_periodicMpvLineMap_family
    (fun γ : unitInterval => arbitraryPhysicalMixedInterpolation A₀ A₁ γ)
    ((continuous_arbitraryPhysicalMixedInterpolation A₀ A₁).comp continuous_subtype_val) N
  have hTinj (γ : unitInterval) :
      Function.Injective (periodicMpvLineMap (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) N) :=
    periodicMpvLineMap_injective_of_mpv_ne_zero _
      (mpv_arbitraryPhysicalMixedInterpolation_ne_zero A₀ A₁ h₀ h₁ γ hN)
  have heq :
      (fun γ : unitInterval => ContinuousLinearMap.injectiveRangeProjector
        (periodicMpvLineMap (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) N) (hTinj γ)) =
      (fun γ : unitInterval => (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN))).starProjection) := by
    funext γ
    rw [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection,
      arbitraryPhysicalMixedInteraction_groundSpace_eq_range A₀ A₁ h₀ h₁ γ hN]
  rw [← heq]
  exact ContinuousLinearMap.continuous_injectiveRangeProjector _ hT hTinj

/-- At each endpoint, the ground projection of the enlarged mixed
Hamiltonian is that of the canonical parent Hamiltonian of the fully
embedded original tensor. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem arbitraryPhysicalMixed_groundSpace_starProjection_endpoint
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (right : Bool) (hN : 2 ≤ N) :
    (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalMixedInteraction A₀ A₁ (if right then 1 else 0)) hN))).starProjection =
    (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointParentInteraction A₀ A₁ right) hN))).starProjection := by
  rw [arbitraryPhysicalMixedInteraction_endpoint_ker_eq_parent A₀ A₁ h₀ h₁ right hN]

/-- As the parameter tends to an endpoint within the closed interval, the
ground projections of the enlarged mixed Hamiltonian converge to the ground
projection of the canonical parent Hamiltonian of the corresponding fully
embedded original tensor. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem tendsto_arbitraryPhysicalMixed_groundSpace_starProjection
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (right : Bool) (hN : 2 ≤ N) :
    Tendsto (fun γ : unitInterval =>
      (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN))).starProjection)
      (𝓝 (if right then 1 else 0))
      (𝓝 (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
        (arbitraryPhysicalEndpointParentInteraction A₀ A₁ right) hN))).starProjection) := by
  rw [← arbitraryPhysicalMixed_groundSpace_starProjection_endpoint A₀ A₁ h₀ h₁ right hN]
  convert (continuous_arbitraryPhysicalMixed_groundSpace_starProjection
    A₀ A₁ h₀ h₁ hN).tendsto (if right then 1 else 0) using 6
  cases right <;> simp

/-- Along either affine attachment, the ground projection is constantly the
canonical parent ground projection. Source: arXiv:2203.12563, Section 5,
lines 1328–1331 and 1690–1692. -/
theorem arbitraryPhysicalEndpointAttachment_groundSpace_starProjection
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (right : Bool) {t : ℝ} (ht : 0 ≤ t) (hN : 2 ≤ N) :
    (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointAttachment A₀ A₁ right t) hN))).starProjection =
    (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointParentInteraction A₀ A₁ right) hN))).starProjection := by
  rw [arbitraryPhysicalEndpointAttachment_ker_eq_parent A₀ A₁ h₀ h₁ right ht hN]

end MPOSymmetry
end MPSTensor
