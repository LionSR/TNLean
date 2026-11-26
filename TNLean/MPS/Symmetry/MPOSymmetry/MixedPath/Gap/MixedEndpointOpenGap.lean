/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointActiveEdgeNormalization
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointZeroSectorGap
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointActiveHamiltonian
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointCoreHamiltonianSpectators
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointRightOpenTransport

/-!
# A derived uniform open gap at the first mixed endpoint

The derived termwise kernel transport identifies both orientations of the
canonical boundary deformation with the actual local projections. The
fixed first- and last-site bounds therefore compare their spectral gaps
with constants independent of the bulk length. The zero-second-sector
comparison supplies an intrinsic ordinary injective-parent gap. The
normalized core is unchanged when the free exterior spectators are
replaced, and the inactive-sector estimate completes the uniform gap
for the actual extended open Hamiltonian.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.

It also contains the following results.

* `MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_open_one_gap`,
  `MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_open_endpoints_gap`: a derived uniform open
  gap at the second mixed endpoint.
-/

section MixedEndpointOpenGap

open scoped BigOperators ComplexOrder

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

open ManyBody.Interaction (chainTranslates)

variable {D₀ D₁ N : ℕ}

/-- The fixed condition factor for both actual boundary coordinate changes. -/
def mixedEndpointBoundaryCondition
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (D₁ : ℕ) : ℝ :=
  mixedEndpointBoundaryForwardBound A₀ hA₀ D₁ ^ 2 *
    mixedEndpointBoundaryInverseBound A₀ hA₀ D₁ ^ 2

/-- Boundary normalization has a strictly positive, volume-independent
condition factor. -/
theorem mixedEndpointBoundaryCondition_pos
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (D₁ : ℕ) :
    0 < mixedEndpointBoundaryCondition A₀ hA₀ D₁ :=
  mul_pos (sq_pos_of_pos (mixedEndpointBoundaryForwardBound_pos A₀ hA₀ D₁))
    (sq_pos_of_pos (mixedEndpointBoundaryInverseBound_pos A₀ hA₀ D₁))

/-- A gap of the actual compressed endpoint gives a gap of the actual
normalized sum, with the derived fixed-boundary loss: if every eigenvalue of
the compressed endpoint is `0` or at least `δ`, then every eigenvalue of the
normalized sum is `0` or at least `δ` divided by the boundary condition factor. -/
theorem mixedEndpointActiveNormalizedHamiltonian_gap_of_actual
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) {δ : ℝ} (hδ : 0 < δ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (mixedEndpointActiveHamiltonian A₀ A₁ (N + 1)) μ → μ = 0 ∨ (δ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N) μ →
        μ = 0 ∨ ((δ / mixedEndpointBoundaryCondition A₀ hA₀ D₁ : ℝ) : ℂ) ≤ μ := by
  let F := activeBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀ (N + 1)
  have hGap' : ∀ μ : ℂ, Module.End.HasEigenvalue (∑ p : MixedEndpointActiveEdgeSite N,
      mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p)) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
    simpa only [← mixedEndpointActiveHamiltonian_eq_sum_edges] using hGap
  have h := F.symm.forall_hasEigenvalue_sum_deformedConstraintProjection
    (fun p : MixedEndpointActiveEdgeSite N =>
      mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p))
    (fun p => mixedEndpointActiveLocalInteraction_isSymmetricProjection A₀ A₁ _)
    (mixedEndpointBoundaryInverseBound_pos A₀ hA₀ D₁)
    (mixedEndpointBoundaryForwardBound_pos A₀ hA₀ D₁) hδ
    (norm_activeBoundaryNormalizationEquivES_symm_apply_le A₀ hA₀)
    (norm_activeBoundaryNormalizationEquivES_apply_le A₀ hA₀) hGap'
  have hden : mixedEndpointBoundaryInverseBound A₀ hA₀ D₁ ^ 2 *
      mixedEndpointBoundaryForwardBound A₀ hA₀ D₁ ^ 2 =
        mixedEndpointBoundaryCondition A₀ hA₀ D₁ := mul_comm _ _
  rw [hden] at h
  simpa only [F, activeBoundaryNormalization_symm_deformed_actualLocal_eq_normalized A₀ A₁ hA₀,
    mixedEndpointActiveNormalizedHamiltonian] using h

/-- Conversely the normalized sum's gap gives a gap of the actual active
Hamiltonian, through its proved canonical local constraints: the lower bound on
the nonzero eigenvalues loses the same boundary condition factor. -/
theorem mixedEndpointActiveHamiltonian_gap_of_normalized
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) {δ : ℝ} (hδ : 0 < δ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N) μ → μ = 0 ∨ (δ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (mixedEndpointActiveHamiltonian A₀ A₁ (N + 1)) μ →
      μ = 0 ∨ ((δ / mixedEndpointBoundaryCondition A₀ hA₀ D₁ : ℝ) : ℂ) ≤ μ := by
  let F := activeBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀ (N + 1)
  have hGap' : ∀ μ : ℂ, Module.End.HasEigenvalue (∑ p : MixedEndpointActiveEdgeSite N,
      mixedEndpointActiveNormalizedLocalInteraction (D₁ := D₁) A₀ p) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := hGap
  have h := F.forall_hasEigenvalue_sum_deformedConstraintProjection
    (fun p : MixedEndpointActiveEdgeSite N =>
      mixedEndpointActiveNormalizedLocalInteraction (D₁ := D₁) A₀ p)
    (mixedEndpointActiveNormalizedLocalInteraction_isSymmetricProjection A₀)
    (mixedEndpointBoundaryForwardBound_pos A₀ hA₀ D₁)
    (mixedEndpointBoundaryInverseBound_pos A₀ hA₀ D₁) hδ
    (norm_activeBoundaryNormalizationEquivES_apply_le A₀ hA₀)
    (norm_activeBoundaryNormalizationEquivES_symm_apply_le A₀ hA₀) hGap'
  simpa only [F, activeBoundaryNormalization_deformed_normalizedLocal_eq_actual A₀ A₁ hA₀,
    ← mixedEndpointActiveHamiltonian_eq_sum_edges, mixedEndpointBoundaryCondition] using h

/-- The actual compressed zero-endpoint Hamiltonian has a positive gap
uniform in all sufficiently large active-chain lengths: every eigenvalue is `0`
or at least the gap. The proof derives
its reference gap from the ordinary injective tensor, then uses the actual
termwise boundary normalizations and the proved free-exterior factorization.
No endpoint gap, local-kernel identity, or reduction is assumed. -/
theorem exists_mixedEndpointActiveHamiltonian_uniform_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    ∃ W : ℕ, 1 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue
        (mixedEndpointActiveHamiltonian A₀ A₁ N) μ → μ = 0 ∨ (δ : ℂ) ≤ μ := by
  by_cases hD₀ : D₀ = 0
  · subst D₀
    refine ⟨1, le_rfl, 1, zero_lt_one, fun N _ μ hμ ↦ ?_⟩
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine absurd ?_ hv.2
    apply PiLp.ext
    rintro ⟨a, ⟨b, σ, c⟩, e⟩
    exact Fin.elim0 b
  · let : NeZero D₀ := ⟨hD₀⟩
    obtain ⟨W, hW, δ, hδ, hGap₀⟩ :=
      exists_mixedEndpointActiveHamiltonian_zeroSector_uniform_gap A₀ hA₀
    let C₀ := mixedEndpointBoundaryCondition A₀ hA₀ 0
    let C₁ := mixedEndpointBoundaryCondition A₀ hA₀ D₁
    have hC₀ : 0 < C₀ := mixedEndpointBoundaryCondition_pos A₀ hA₀ 0
    have hC₁ : 0 < C₁ := mixedEndpointBoundaryCondition_pos A₀ hA₀ D₁
    have hδ' : 0 < δ / C₀ := div_pos hδ hC₀
    refine ⟨max 1 W, le_max_left _ _, δ / C₀ / C₁, div_pos hδ' hC₁, ?_⟩
    intro N hWN
    cases N with
    | zero => have := le_max_left 1 W; omega
    | succ n =>
      have hGapZero := mixedEndpointActiveNormalizedHamiltonian_gap_of_actual
        A₀ emptyEndpointTensor hA₀ hδ (hGap₀ (n + 1) (by omega))
      exact mixedEndpointActiveHamiltonian_gap_of_normalized A₀ A₁ hA₀ hδ' fun μ hμ ↦
        hGapZero μ
          ((mixedEndpointActiveNormalizedHamiltonian_hasEigenvalue_iff_zeroSector
            (D₁ := D₁) A₀ n μ).mp hμ)

/-- The nonzero eigenvalues of the actual extended first-endpoint open Hamiltonian have a
positive volume-independent lower bound for all sufficiently large windows. The inactive
sectors contribute the derived one-half lower bound. The two exterior
registers remain free, so no smaller padded-endpoint ground space is used.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_uniform_mixedEndpoint_open_zero_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    ∃ W : ℕ, 3 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
          (chainTranslates 2 N (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨W, hW, δ, hδ, hGap⟩ :=
    exists_mixedEndpointActiveHamiltonian_uniform_gap A₀ A₁ hA₀
  refine ⟨W + 1 + 1, by omega, min δ (1 / 2), lt_min hδ (by norm_num), ?_⟩
  intro N hWN
  have hlen : N - 2 + 1 + 1 = N := by omega
  rw [← hlen]
  exact mixedEndpoint_open_gap_of_active_gap A₀ A₁ (hGap (N - 2) (by omega))

end
end MPOSymmetry
end MPSTensor

end MixedEndpointOpenGap

section MixedEndpointRightOpenGap

/-!
## A derived uniform open gap at the second mixed endpoint

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
  intro N hWN μ hμ
  exact hGap N hWN μ ((ManyBody.hasEigenvalue_iff_of_intertwine
    (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) N).toLinearEquiv
    (mixedEndpoint_hamiltonian_chainTranslates_one_apply_swap A₀ A₁ N) μ).mp hμ)

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

end MixedEndpointRightOpenGap
