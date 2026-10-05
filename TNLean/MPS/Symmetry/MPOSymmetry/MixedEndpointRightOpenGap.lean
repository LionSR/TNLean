/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenGap
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointRightOpenTransport

/-!
# A derived uniform open gap at the second mixed endpoint

The actual second-endpoint open Hamiltonian is unitarily conjugate to the
first-endpoint Hamiltonian for the reversed pair. Its uniform gap therefore
follows from the bounded-boundary comparison already proved at zero, with
no change in the constant and no assumption about its ground space.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped InnerProductSpace

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- The actual extended second-endpoint open Hamiltonian has a positive
gap uniform in all sufficiently large windows. Its reference gap, sector
reduction, local projections, and kernel transport are derived. -/
theorem exists_uniform_mixedEndpoint_open_one_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) :
    ∃ W : ℕ, 3 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N v‖ := by
  obtain ⟨W, hW, δ, hδ, hGap⟩ := exists_uniform_mixedEndpoint_open_zero_gap A₁ A₀ hA₁
  refine ⟨W, hW, δ, hδ, ?_⟩
  intro N hWN v hv
  let U := physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N
  let H := openInteractionHamiltonianES (mixedEndpointParentInteraction A₁ A₀ 0).toLinearMap N
  let K := openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N
  have hintertwine (x : EuclideanSpace ℂ (Cfg ((D₁ + D₀) * (D₁ + D₀)) N)) :
      K (U x) = U (H x) :=
    mixedEndpoint_openInteractionHamiltonian_one_apply_swap A₀ A₁ N x
  have hperp : U.symm v ∈ (LinearMap.ker H)ᗮ := by
    apply Submodule.mem_orthogonal.mpr
    intro z hz
    have hz' : U z ∈ LinearMap.ker K := by
      change K (U z) = 0
      rw [hintertwine, LinearMap.mem_ker.mp hz, map_zero]
    have h := (Submodule.mem_orthogonal.mp hv) (U z) hz'
    rw [← U.inner_map_map z (U.symm v), U.apply_symm_apply]
    exact h
  have h := hGap N hWN (U.symm v) hperp
  rw [U.symm.norm_map] at h
  have hKv : K v = U (H (U.symm v)) := by
    simpa only [U.apply_symm_apply] using hintertwine (U.symm v)
  change δ * ‖v‖ ≤ ‖K v‖
  rw [hKv, U.norm_map]
  exact h

/-- One eventual open-gap bound works at both endpoints, retaining the
actual extended ground spaces at each end. -/
theorem exists_uniform_mixedEndpoint_open_endpoints_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁) :
    ∃ W : ℕ, 3 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ p : ℝ, p = 0 ∨ p = 1 → ∀ N : ℕ, W ≤ N →
        ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ p).toLinearMap N))ᗮ,
          δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
            (mixedEndpointParentInteraction A₀ A₁ p).toLinearMap N v‖ := by
  obtain ⟨W₀, hW₀, δ₀, hδ₀, hGap₀⟩ := exists_uniform_mixedEndpoint_open_zero_gap A₀ A₁ hA₀
  obtain ⟨W₁, hW₁, δ₁, hδ₁, hGap₁⟩ := exists_uniform_mixedEndpoint_open_one_gap A₀ A₁ hA₁
  refine ⟨max W₀ W₁, hW₀.trans (le_max_left _ _), min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  rintro p (rfl | rfl) N hWN v hv
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans
      (hGap₀ N ((le_max_left _ _).trans hWN) v hv)
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans
      (hGap₁ N ((le_max_right _ _).trans hWN) v hv)

end MPOSymmetry
end MPSTensor
