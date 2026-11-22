/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.FixedPoint.FixedPointGappedPath
import TNLean.MPS.Operator.Interaction.GappedInteractionPath
import TNLean.MPS.Symmetry.FixedPoint.BondProductPhysicalParentHamiltonian
import TNLean.MPS.Symmetry.FixedPoint.BondProductSpectralGap
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import QICLean.Algebra.Unitary.IsometricFrameEmbedding
import TNLean.MPS.ParentHamiltonian.ParentInteraction.PhysicalDeformation

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

## Local symmetry of the normalized bond interpolation

Every two-site term of the normalized direct-sum bond interpolation is
invariant under the physical on-site symmetry.
Source: arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym.
-/

section

open scoped Matrix Matrix.Norms.L2Operator

namespace MPSTensor

/-- For a pointwise unitary projective virtual action, the physical action
`U(g) = W_gᵀ ⊗ W_g⁻¹` of the fixed-point tensor as a unitary representation.
Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
noncomputable def sptFixedPointUnitaryAction
    {G : Type} [Group G] {D : ℕ}
    {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ) :
    G →* Matrix.unitaryGroup (Fin (D * D)) ℂ :=
  (sptFixedPointAction ρ 1).codRestrict (Matrix.unitaryGroup (Fin (D * D)) ℂ)
    (sptFixedPointAction_mem_unitaryGroup ρ 1 hρ (fun _ => by simp))

/-- The normalized interpolation is a symmetric gapped interaction path
between its endpoint fixed-point interactions. Its local term has norm at
most one, and the finite-chain gap is uniformly at least one.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
noncomputable def normalizedBondFixedPointGappedPath
    {G : Type} [Group G] {D₀ D₁ : ℕ}
    {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω)
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
      rw [@hamiltonian_translationInvariant_twoSiteBondPenalty (D₀ + D₁) N hNZ hN]
      exact (normalizedPhysicalBondInterpolation_parent_spectrum_gap_one
        hD₀ hD₁ γ (by omega)).1
    · intro z hz
      unfold normalizedBondInteraction at hz
      rw [@hamiltonian_translationInvariant_twoSiteBondPenalty (D₀ + D₁) N hNZ hN] at hz
      have h := (normalizedPhysicalBondInterpolation_parent_spectrum_gap_one
        hD₀ hD₁ γ (by omega)).2 z hz
      simpa using h
  symmetric γ hγ g N hN := by
    have hNZ : NeZero N := ⟨by omega⟩
    unfold normalizedBondInteraction
    rw [@hamiltonian_translationInvariant_twoSiteBondPenalty (D₀ + D₁) N hNZ hN]
    change Commute
      (physicalBondProductParentHamiltonian
        (normalizedBondInterpolationVector D₀ D₁ γ) (by omega))
      (Matrix.finKronecker (fun _ : Fin N =>
        sptFixedPointAction (ρ₀.directSum ρ₁) 1 g))
    exact (normalizedPhysicalBondInterpolation_parent_commute_onSite
      ρ₀ ρ₁ h₀ h₁ g γ (by omega)).symm

end MPSTensor

end

section

open scoped Matrix Kronecker

namespace MPSTensor

/-- Each local normalized bond interaction commutes with the two-site
physical symmetry. Source: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem normalizedBondInteraction_commute_onSite
    {G : Type} [Group G] {D₀ D₁ : ℕ}
    {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (g : G) (γ : ℝ) :
    Commute (normalizedBondInteraction D₀ D₁ γ)
      (onSiteTensorPow 2 (sptFixedPointAction (ρ₀.directSum ρ₁) 1 g)) := by
  let ρ := ρ₀.directSum ρ₁
  let X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ := ρ.X g⁻¹
  let S := Matrix.reindex finProdFinEquiv finProdFinEquiv (Xᴴ ⊗ₖ Xᵀ)
  have hX : X ∈ Matrix.unitaryGroup (Fin (D₀ + D₁)) ℂ :=
    ρ₀.directSum_mem_unitaryGroup ρ₁ g⁻¹ (h₀ g⁻¹) (h₁ g⁻¹)
  have hS : S ∈ Matrix.unitaryGroup (Fin ((D₀ + D₁) * (D₀ + D₁))) ℂ :=
    Matrix.reindex_mem_unitaryGroup finProdFinEquiv (Xᴴ ⊗ₖ Xᵀ)
      (Matrix.kronecker_mem_unitary (Unitary.star_mem hX)
        (Matrix.transpose_mem_unitaryGroup_iff.mpr hX))
  have hfix : S *ᵥ normalizedBondInterpolationVector D₀ D₁ γ =
      normalizedBondInterpolationVector D₀ D₁ γ :=
    normalizedBondInterpolationVector_fixed_directSum
      ρ₀ ρ₁ g⁻¹ γ (h₀ g⁻¹) (h₁ g⁻¹)
  let P := (incomingBondPerm (D₀ + D₁) 2).permMatrix ℂ
  let U : Matrix.unitaryGroup (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) ℂ :=
    ⟨P, incomingBondPerm_mem_unitaryGroup (D₀ + D₁) 2⟩
  have hlocal :=
    (bondPenaltyAt_commute_sitewise_of_unitary_fixed (N := 2)
      (normalizedBondInterpolationVector D₀ D₁ γ) S hS hfix (by omega)
      (finRotate 2 0)).map (Unitary.conjStarAlgAut ℂ _ U)
  simp only [Unitary.conjStarAlgAut_apply, U, Matrix.star_eq_conjTranspose] at hlocal
  have haction : P * Matrix.rectKronecker (fun _ : Fin 2 => S) * Pᴴ =
      onSiteTensorPow 2 (sptFixedPointAction ρ 1 g) := by
    change P * Matrix.finKronecker (fun _ : Fin 2 => S) * Pᴴ = _
    simpa only [P, S, X, onSiteTensorPow_eq_finKronecker,
      Matrix.rectKronecker_apply, Matrix.finKronecker_apply, sptGauge,
      Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup (ρ.X g⁻¹) hX] using
        incomingBondPerm_conj_sptFixedPointAction ρ g 2
  have hBond : P * bondPenaltyAt (normalizedBondInterpolationVector D₀ D₁ γ)
      (by omega) (finRotate 2 0) * Pᴴ = normalizedBondInteraction D₀ D₁ γ := by
    have h := embed_twoSiteBondInteraction_eq_conj (N := 2) (by omega) 0
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ)))
    have hw : ManyBody.ringWindow (by omega : 2 ≤ 2) (0 : Fin 2) =
        Function.Embedding.refl (Fin 2) := by
      ext j
      fin_cases j <;> rfl
    rw [hw, ManyBody.placeAlong_refl] at h
    simpa only [normalizedBondInteraction, bondPenaltyAt, P,
      ← Matrix.reindex_symm, Equiv.apply_symm_apply] using h.symm
  rw [haction, hBond] at hlocal
  exact hlocal.symm

end MPSTensor

end
