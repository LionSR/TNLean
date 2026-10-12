/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveEdgeNormalization
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointZeroSectorGap
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveGapTransfer
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointCoreHamiltonianSpectators

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
-/

open scoped BigOperators

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

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
normalized sum, with the derived fixed-boundary loss. -/
theorem mixedEndpointActiveNormalizedHamiltonian_norm_gap_of_actual
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) {δ : ℝ} (hδ : 0 < δ)
    (hGap : ∀ v ∈ (LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ (N + 1)))ᗮ,
      δ * ‖v‖ ≤ ‖mixedEndpointActiveHamiltonian A₀ A₁ (N + 1) v‖) :
    ∀ v ∈ (LinearMap.ker (mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N))ᗮ,
      (δ / mixedEndpointBoundaryCondition A₀ hA₀ D₁) * ‖v‖ ≤
        ‖mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N v‖ := by
  let F := activeBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀ (N + 1)
  have hGap' : ∀ v ∈ (LinearMap.ker (∑ p : MixedEndpointActiveEdgeSite N,
      mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p)))ᗮ,
      δ * ‖v‖ ≤ ‖(∑ p : MixedEndpointActiveEdgeSite N,
        mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p)) v‖ := by
    simpa only [← mixedEndpointActiveHamiltonian_eq_sum_edges] using hGap
  have h := F.symm.norm_gap_sum_deformedConstraintProjection
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
Hamiltonian, through its proved canonical local constraints. -/
theorem mixedEndpointActiveHamiltonian_norm_gap_of_normalized
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) {δ : ℝ} (hδ : 0 < δ)
    (hGap : ∀ v ∈ (LinearMap.ker
      (mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N))ᗮ,
      δ * ‖v‖ ≤ ‖mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N v‖) :
    ∀ v ∈ (LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ (N + 1)))ᗮ,
      (δ / mixedEndpointBoundaryCondition A₀ hA₀ D₁) * ‖v‖ ≤
        ‖mixedEndpointActiveHamiltonian A₀ A₁ (N + 1) v‖ := by
  let F := activeBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀ (N + 1)
  have hGap' : ∀ v ∈ (LinearMap.ker (∑ p : MixedEndpointActiveEdgeSite N,
      mixedEndpointActiveNormalizedLocalInteraction (D₁ := D₁) A₀ p))ᗮ,
      δ * ‖v‖ ≤ ‖(∑ p : MixedEndpointActiveEdgeSite N,
        mixedEndpointActiveNormalizedLocalInteraction (D₁ := D₁) A₀ p) v‖ := hGap
  have h := F.norm_gap_sum_deformedConstraintProjection
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
uniform in all sufficiently large active-chain lengths. The proof derives
its reference gap from the ordinary injective tensor, then uses the actual
termwise boundary normalizations and the proved free-exterior factorization.
No endpoint gap, local-kernel identity, or reduction is assumed. -/
theorem exists_mixedEndpointActiveHamiltonian_uniform_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    ∃ W : ℕ, 1 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ v ∈ (LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ N))ᗮ,
        δ * ‖v‖ ≤ ‖mixedEndpointActiveHamiltonian A₀ A₁ N v‖ := by
  by_cases hD₀ : D₀ = 0
  · subst D₀
    refine ⟨1, le_rfl, 1, zero_lt_one, ?_⟩
    intro N _ v _
    have hv : v = 0 := by
      apply PiLp.ext
      rintro ⟨a, ⟨b, σ, c⟩, e⟩
      exact Fin.elim0 b
    simp [hv]
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
      have hNorm₀ := mixedEndpointActiveNormalizedHamiltonian_norm_gap_of_actual
        A₀ emptyEndpointTensor hA₀ hδ (hGap₀ (n + 1) (by omega))
      have hNorm := (mixedEndpointActiveNormalizedHamiltonian_norm_gap_iff_zeroSector
        (D₁ := D₁) A₀ n hδ'.le).mpr hNorm₀
      exact mixedEndpointActiveHamiltonian_norm_gap_of_normalized A₀ A₁ hA₀ hδ' hNorm

/-- The actual extended first-endpoint open Hamiltonian has a positive
volume-independent gap for all sufficiently large windows. The inactive
sectors contribute the derived one-half lower bound. The two exterior
registers remain free, so no smaller padded-endpoint ground space is used.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_uniform_mixedEndpoint_open_zero_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    ∃ W : ℕ, 3 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N v‖ := by
  obtain ⟨W, hW, δ, hδ, hGap⟩ :=
    exists_mixedEndpointActiveHamiltonian_uniform_gap A₀ A₁ hA₀
  refine ⟨W + 1 + 1, by omega, min δ (1 / 2), lt_min hδ (by norm_num), ?_⟩
  intro N hWN
  have hlen : N - 2 + 1 + 1 = N := by omega
  rw [← hlen]
  exact mixedEndpoint_open_norm_gap_of_active_norm_gap A₀ A₁ hδ.le
    (hGap (N - 2) (by omega))

end
end MPOSymmetry
end MPSTensor
