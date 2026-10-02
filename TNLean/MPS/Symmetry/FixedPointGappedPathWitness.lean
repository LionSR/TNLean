/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.FixedPointGappedPath
import TNLean.MPS.Symmetry.GappedInteractionPath
import TNLean.MPS.Symmetry.BondProductPhysicalSymmetry
import TNLean.MPS.Symmetry.BondProductSpectralGap

/-!
# A symmetric gapped path between the direct-sum fixed points

The normalized interpolation of the two maximally entangled bond states
defines a translation-invariant nearest-neighbor interaction on one common
physical space. Its finite-chain Hamiltonians have a uniform gap of one
and commute with a fixed on-site unitary representation. This is the
fixed-point part of Schuch--Pérez-García--Cirac, arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`.

This statement concerns the direct-sum fixed points. It does not identify
arbitrary injective symmetric MPS with those endpoints.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace MPSTensor

/-- For a pointwise unitary projective virtual action, the physical action
`U(g) = W_gᵀ ⊗ W_g⁻¹` of the fixed-point tensor as a unitary representation.
Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
noncomputable def sptFixedPointUnitaryAction
    {G : Type} [Group G] {D : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ) :
    G →* Matrix.unitaryGroup (Fin (D * D)) ℂ :=
  (sptFixedPointAction ρ 1).codRestrict (Matrix.unitaryGroup (Fin (D * D)) ℂ)
    (sptFixedPointAction_mem_unitaryGroup ρ hρ)

/-- The normalized interpolation is a symmetric gapped interaction path
between its endpoint fixed-point interactions. Its local term has norm at
most one, and the finite-chain gap is uniformly at least one.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
noncomputable def normalizedBondFixedPointGappedPath
    {G : Type} [Group G] {D₀ D₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈
      Matrix.unitaryGroup (Fin D₀) ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈
      Matrix.unitaryGroup (Fin D₁) ℂ) :
    SymmetricGappedInteractionPath
      (sptFixedPointUnitaryAction (ρ₀.directSum ρ₁)
        (fun g => ρ₀.directSum_mem_unitaryGroup ρ₁ g (h₀ g) (h₁ g)))
      (normalizedBondInteraction D₀ D₁ 0)
      (normalizedBondInteraction D₀ D₁ 1) where
  interaction := normalizedBondInteraction D₀ D₁
  interaction_zero := rfl
  interaction_one := rfl
  hermitian γ hγ := by
    have h := normalizedBondInteraction_isStarProjection hD₀ hD₁ γ
    simpa only [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using
      h.isSelfAdjoint.star_eq
  norm_le_one γ hγ :=
    (normalizedBondInteraction_isStarProjection hD₀ hD₁ γ).norm_le _
  continuous :=
    (continuous_normalizedBondInteraction hD₀ hD₁).continuousOn
  gap := by
    refine ⟨1, by norm_num, ?_⟩
    intro γ hγ N hN
    have hNZ : NeZero N := ⟨by omega⟩
    refine ⟨0, ?_, ?_⟩
    · unfold normalizedBondInteraction
      rw [@interactionHamiltonian_twoSiteBondPenalty (D₀ + D₁) N hNZ]
      exact (normalizedPhysicalBondInterpolation_parent_spectrum_gap_one
        hD₀ hD₁ γ (by omega)).1
    · intro z hz
      unfold normalizedBondInteraction at hz
      rw [@interactionHamiltonian_twoSiteBondPenalty (D₀ + D₁) N hNZ] at hz
      have h := (normalizedPhysicalBondInterpolation_parent_spectrum_gap_one
        hD₀ hD₁ γ (by omega)).2 z hz
      simpa using h
  symmetric γ hγ g N hN := by
    have hNZ : NeZero N := ⟨by omega⟩
    unfold normalizedBondInteraction
    rw [@interactionHamiltonian_twoSiteBondPenalty (D₀ + D₁) N hNZ]
    change Commute
      (physicalBondProductParentHamiltonian
        (normalizedBondInterpolationVector D₀ D₁ γ) (by omega))
      (Matrix.finKronecker (fun _ : Fin N =>
        sptFixedPointAction (ρ₀.directSum ρ₁) 1 g))
    exact (normalizedPhysicalBondInterpolation_parent_commute_onSite
      ρ₀ ρ₁ h₀ h₁ g γ (by omega)).symm

end MPSTensor
