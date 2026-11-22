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

open scoped InnerProductSpace ComplexOrder

namespace MPSTensor
namespace MPOSymmetry

open ManyBody.Interaction (chainTranslates)

variable {D₀ D₁ : ℕ}

/-- The nonzero eigenvalues of the actual extended second-endpoint open Hamiltonian have a
positive lower bound uniform in all sufficiently large windows. Its reference gap, sector
reduction, local projections, and kernel transport are derived. -/
theorem exists_uniform_mixedEndpoint_open_one_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) :
    ∃ W : ℕ, 3 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
          (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨W, hW, δ, hδ, hGap⟩ := exists_uniform_mixedEndpoint_open_zero_gap A₁ A₀ hA₁
  refine ⟨W, hW, δ, hδ, ?_⟩
  intro N hWN
  refine (ManyBody.forall_hasEigenvalue_iff_norm
    (ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ 1) N)).mpr ?_
  intro v hv
  let U := physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N
  let H := Matrix.toEuclideanLin (chainTranslates 2 N
      (mixedEndpointParentInteraction A₁ A₀ 0)).hamiltonian
  let K := Matrix.toEuclideanLin (chainTranslates 2 N
      (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian
  have hintertwine (x : EuclideanSpace ℂ (Cfg ((D₁ + D₀) * (D₁ + D₀)) N)) :
      K (U x) = U (H x) :=
    mixedEndpoint_hamiltonian_chainTranslates_one_apply_swap A₀ A₁ N x
  have hperp : U.symm v ∈ (LinearMap.ker H)ᗮ := by
    apply ((LinearMap.ker H).mem_orthogonal (U.symm v)).mpr
    intro z hz
    have hz' : U z ∈ LinearMap.ker K := by
      change K (U z) = 0
      rw [hintertwine, LinearMap.mem_ker.mp hz, map_zero]
    have h := ((LinearMap.ker K).mem_orthogonal v).mp hv (U z) hz'
    rw [← U.inner_map_map z (U.symm v), U.apply_symm_apply]
    exact h
  have h := (ManyBody.forall_hasEigenvalue_iff_norm
    (ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates
      (posSemidef_mixedEndpointParentInteraction A₁ A₀ 0) N)).mp (hGap N hWN) (U.symm v) hperp
  rw [U.symm.norm_map] at h
  have hKv : K v = U (H (U.symm v)) := by
    simpa only [U.apply_symm_apply] using hintertwine (U.symm v)
  change δ * ‖v‖ ≤ ‖K v‖
  rw [hKv, U.norm_map]
  exact h

/-- One eventual lower bound on the nonzero eigenvalues works at both endpoints, retaining the
actual extended ground spaces at each end. -/
theorem exists_uniform_mixedEndpoint_open_endpoints_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁) :
    ∃ W : ℕ, 3 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ p : ℝ, p = 0 ∨ p = 1 → ∀ N : ℕ, W ≤ N →
        ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
            (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ p)).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨W₀, hW₀, δ₀, hδ₀, hGap₀⟩ := exists_uniform_mixedEndpoint_open_zero_gap A₀ A₁ hA₀
  obtain ⟨W₁, hW₁, δ₁, hδ₁, hGap₁⟩ := exists_uniform_mixedEndpoint_open_one_gap A₀ A₁ hA₁
  refine ⟨max W₀ W₁, hW₀.trans (le_max_left _ _), min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  rintro p (rfl | rfl) N hWN
  · exact ManyBody.forall_hasEigenvalue_mono (min_le_left _ _)
      (hGap₀ N ((le_max_left _ _).trans hWN))
  · exact ManyBody.forall_hasEigenvalue_mono (min_le_right _ _)
      (hGap₁ N ((le_max_right _ _).trans hWN))

end MPOSymmetry
end MPSTensor
