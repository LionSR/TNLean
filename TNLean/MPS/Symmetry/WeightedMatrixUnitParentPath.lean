/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.WeightedMatrixUnitParent
import TNLean.MPS.Symmetry.OrderedGappedInteractionPath
import TNLean.MPS.Symmetry.FixedPointGappedPathWitness
import TNLean.MPS.Symmetry.InteractionHamiltonianSymmetry
import TNLean.MPS.Symmetry.GappedInteractionPathComposition

/-!
# Gapped paths between weighted canonical parents

For each fixed interpolation parameter, compare the independent-bond
interaction with the canonical parent of the weighted matrix-unit tensor.
They have the same periodic ground line, so the affine comparison retains
the gap of one. Concatenating the endpoint comparisons with the continuous
bond path connects the two canonical endpoint parents.

Source: arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`.
This construction concerns the common direct-sum physical space. It does
not identify arbitrary isometric tensors with the weighted endpoints.

**Scope restriction (trivial character):** The path constructors use the
on-site action with trivial scalar character; see
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MPSTensor

/-- The periodic normalized-bond Hamiltonian has zero ground energy and
spectral gap at least one for every real parameter. Source:
arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem interactionHamiltonian_normalizedBondInteraction_spectrum_gap_one
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N) :
    (0 : ℂ) ∈ spectrum ℂ (interactionHamiltonian
      (normalizedBondInteraction D₀ D₁ γ) hN) ∧
    ∀ z ∈ spectrum ℂ (interactionHamiltonian
      (normalizedBondInteraction D₀ D₁ γ) hN),
      0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  have : NeZero N := ⟨by omega⟩
  simpa only [normalizedBondInteraction, interactionHamiltonian_twoSiteBondPenalty] using
    normalizedPhysicalBondInterpolation_parent_spectrum_gap_one h₀ h₁ γ (by omega : 1 ≤ N)

/-- For a fixed bond parameter, affine interpolation to a covariant
canonical parent retains the uniform gap when the parent dominates the
bond interaction and annihilates its periodic zero modes.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`,
comparison of the fixed-point parent interactions. -/
noncomputable def normalizedBondCanonicalParentComparisonPath
    {G : Type} [Group G] {D₀ D₁ E : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈
      Matrix.unitaryGroup (Fin D₀) ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈
      Matrix.unitaryGroup (Fin D₁) ℂ) (γ : ℝ)
    (B : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) E)
    (horder : normalizedBondInteraction D₀ D₁ γ ≤
      LinearMap.toMatrix' (parentInteraction B 2))
    (hker : ∀ (N : ℕ) (hN : 2 ≤ N) (x : Cfg ((D₀ + D₁) * (D₀ + D₁)) N → ℂ),
      (interactionHamiltonian (normalizedBondInteraction D₀ D₁ γ) hN).mulVec x = 0 →
        (interactionHamiltonian (LinearMap.toMatrix' (parentInteraction B 2)) hN).mulVec x = 0)
    (hCov : ∀ g, GaugeEquiv B (rotatePhysical (sptFixedPointAction (ρ₀.directSum ρ₁) 1 g) B)) :
    SymmetricGappedInteractionPath
      (sptFixedPointUnitaryAction (ρ₀.directSum ρ₁)
        (fun g => ρ₀.directSum_mem_unitaryGroup ρ₁ g (h₀ g) (h₁ g)))
      (normalizedBondInteraction D₀ D₁ γ)
      (LinearMap.toMatrix' (parentInteraction B 2)) := by
  refine orderedGappedInteractionPath _ _ _
    (Matrix.nonneg_iff_posSemidef.mp
      (normalizedBondInteraction_isStarProjection hD₀ hD₁ γ).nonneg)
    (Matrix.nonneg_iff_posSemidef.mp
      (parentInteraction_toMatrix'_isStarProjection _ 2).nonneg)
    horder
    ((normalizedBondInteraction_isStarProjection hD₀ hD₁ γ).norm_le _)
    (parentInteraction_toMatrix'_norm_le_one _ 2)
    hker ?_ ?_ ?_ ?_
  case refine_4 =>
    intro N hN g
    exact interactionHamiltonian_commute_onSiteTensorPow
      (sptFixedPointAction (ρ₀.directSum ρ₁) 1 g) _ hN
        (parentInteraction_matrix_commute_onSiteTensorPow _ _
          (sptFixedPointAction_mem_unitaryGroup _ 1
            (fun g => ρ₀.directSum_mem_unitaryGroup ρ₁ g (h₀ g) (h₁ g))
            (fun _ => by simp) g) (hCov g) 2)
  case refine_3 =>
    intro N hN g
    have : NeZero N := ⟨by omega⟩
    simpa only [normalizedBondInteraction, interactionHamiltonian_twoSiteBondPenalty,
      sptFixedPointUnitaryAction, MonoidHom.codRestrict_apply, Subtype.coe_mk] using
      (normalizedPhysicalBondInterpolation_parent_commute_onSite
        ρ₀ ρ₁ h₀ h₁ g γ (by omega : 1 ≤ N)).symm
  case refine_2 =>
    exact ⟨1, zero_lt_one, fun N hN z hz =>
      ((interactionHamiltonian_normalizedBondInteraction_spectrum_gap_one
        hD₀ hD₁ γ hN).2 z hz).2⟩
  case refine_1 =>
    intro N hN
    have hspec : (0 : ℂ) ∈ spectrum ℂ (Matrix.toEuclideanLin
        (interactionHamiltonian (normalizedBondInteraction D₀ D₁ γ) hN)) := by
      rw [Matrix.spectrum_toLpLin]
      exact (interactionHamiltonian_normalizedBondInteraction_spectrum_gap_one
        hD₀ hD₁ γ hN).1
    obtain ⟨x, hx⟩ :=
      (Module.End.HasEigenvalue.of_mem_spectrum hspec).exists_hasEigenvector
    exact ⟨x, hx.2, by simpa only [zero_smul] using hx.apply_eq_smul⟩

/-- For a fixed bond parameter, affine interpolation from its bond
interaction to its canonical parent is symmetric and uniformly gapped.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`,
comparison of the fixed-point parent interactions. -/
noncomputable def weightedMatrixUnitParentComparisonPath
    {G : Type} [Group G] {D₀ D₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈
      Matrix.unitaryGroup (Fin D₀) ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈
      Matrix.unitaryGroup (Fin D₁) ℂ) (γ : ℝ) :
    SymmetricGappedInteractionPath
      (sptFixedPointUnitaryAction (ρ₀.directSum ρ₁)
        (fun g => ρ₀.directSum_mem_unitaryGroup ρ₁ g (h₀ g) (h₁ g)))
      (normalizedBondInteraction D₀ D₁ γ)
      (LinearMap.toMatrix' (parentInteraction
        (weightedMatrixUnitInterpolation D₀ D₁ γ) 2)) :=
  normalizedBondCanonicalParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ γ
    (weightedMatrixUnitInterpolation D₀ D₁ γ)
    (twoSiteBondInteraction_le_parentInteraction_weightedMatrixUnitInterpolation hD₀ hD₁ γ)
    (fun _ hN x hx =>
      interactionHamiltonian_parent_mulVec_eq_zero_of_normalizedBondInteraction
        hD₀ hD₁ γ hN x hx)
    (fun g => ⟨sptGauge (ρ₀.directSum ρ₁) g,
      twistedTensor_weightedMatrixUnitInterpolation ρ₀ ρ₁ g γ⟩)

/-- The canonical parents of the two weighted fixed-point endpoints are
connected on their common physical space by a symmetric gapped path.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`.
The endpoint tensors may have vanishing coefficients. -/
noncomputable def weightedCanonicalFixedPointGappedPath
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
      (LinearMap.toMatrix' (parentInteraction
        (weightedMatrixUnitInterpolation D₀ D₁ 0) 2))
      (LinearMap.toMatrix' (parentInteraction
        (weightedMatrixUnitInterpolation D₀ D₁ 1) 2)) :=
  ((weightedMatrixUnitParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ 0).reverse.trans
    (normalizedBondFixedPointGappedPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁)).trans
      (weightedMatrixUnitParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ 1)

end MPSTensor
