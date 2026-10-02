/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.EmbeddedFixedPointTensor
import TNLean.MPS.Symmetry.WeightedMatrixUnitParentPath

/-!
# Gapped canonical parents of the embedded fixed-point endpoints

The smaller endpoint tensors are compared with the independent-bond
interactions on the common physical space. Boundary-space inclusion gives
the local operator inequality; equality of their positive-length periodic
vectors gives the common periodic zero modes. These are the endpoint
comparisons in arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`.

**Scope restriction (trivial character):** The three path constructors use
the on-site action with trivial scalar character; see
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace MPSTensor

/-- An isometric bond restriction of the weighted tensor has canonical
parent interaction at least as large as the independent-bond interaction.
Source context: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`,
restriction to an occupied endpoint summand. -/
theorem normalizedBondInteraction_le_parent_of_isometric_bond_intertwiner
    {D₀ D₁ E : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ)
    (B : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) E)
    (V : Matrix (Fin (D₀ + D₁)) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, weightedMatrixUnitInterpolation D₀ D₁ γ i * V = V * B i) :
    normalizedBondInteraction D₀ D₁ γ ≤ LinearMap.toMatrix' (parentInteraction B 2) := by
  refine twoSiteBondInteraction_le_parentInteraction_of_groundSpaceMap B _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) ?_
  intro X
  simpa only [groundSpaceMap_eq_of_isometric_bond_intertwiner _ B V hV hInt] using
    twoSiteBondInteraction_groundSpaceMap_weightedMatrixUnitInterpolation h₀ h₁ γ
      (V * X * Vᴴ)

/-- The first embedded canonical parent is joined to the first bond
interaction by a symmetric affine path with a uniform gap.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`
and `eq:1d-sym:jointsym`, the first endpoint comparison. -/
noncomputable def embeddedSptFixedPointLeftParentComparisonPath
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
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
      (LinearMap.toMatrix' (parentInteraction (embeddedSptFixedPointLeft D₀ D₁) 2)) :=
  normalizedBondCanonicalParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ 0
    (embeddedSptFixedPointLeft D₀ D₁)
    (normalizedBondInteraction_le_parent_of_isometric_bond_intertwiner hD₀ hD₁ 0 _
      (Matrix.coordinateInclusion (Fin.castAddEmb D₁))
      (Matrix.coordinateInclusion_isometry (Fin.castAddEmb D₁))
      (weightedMatrixUnitInterpolation_zero_intertwine D₀ D₁))
    (fun _ hN x hx =>
      interactionHamiltonian_parent_mulVec_eq_zero_of_normalizedBondInteraction_of_mpv_eq
        hD₀ hD₁ 0 hN _ (mpv_embeddedSptFixedPointLeft (by omega)) x hx)
    (fun g => ⟨sptGauge ρ₀ g, twistedTensor_embeddedSptFixedPointLeft ρ₀ ρ₁ g⟩)
/-- The second embedded canonical parent is joined to the second bond
interaction by a symmetric affine path with a uniform gap.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`
and `eq:1d-sym:jointsym`, the second endpoint comparison. -/
noncomputable def embeddedSptFixedPointRightParentComparisonPath
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
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
      (normalizedBondInteraction D₀ D₁ 1)
      (LinearMap.toMatrix' (parentInteraction (embeddedSptFixedPointRight D₀ D₁) 2)) :=
  normalizedBondCanonicalParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ 1
    (embeddedSptFixedPointRight D₀ D₁)
    (normalizedBondInteraction_le_parent_of_isometric_bond_intertwiner hD₀ hD₁ 1 _
      (Matrix.coordinateInclusion (Fin.natAddEmb D₀))
      (Matrix.coordinateInclusion_isometry (Fin.natAddEmb D₀))
      (weightedMatrixUnitInterpolation_one_intertwine D₀ D₁))
    (fun _ hN x hx =>
      interactionHamiltonian_parent_mulVec_eq_zero_of_normalizedBondInteraction_of_mpv_eq
        hD₀ hD₁ 1 hN _ (mpv_embeddedSptFixedPointRight (by omega)) x hx)
    (fun g => ⟨sptGauge ρ₁ g, twistedTensor_embeddedSptFixedPointRight ρ₀ ρ₁ g⟩)

/-- The canonical parents of the two physically embedded fixed points are
connected by a symmetric uniformly gapped path on the common physical
space. Each tensor retains its original bond dimension. Source:
arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`
and `eq:1d-sym:jointsym`. -/
noncomputable def embeddedCanonicalFixedPointGappedPath
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
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
      (LinearMap.toMatrix' (parentInteraction (embeddedSptFixedPointLeft D₀ D₁) 2))
      (LinearMap.toMatrix' (parentInteraction (embeddedSptFixedPointRight D₀ D₁) 2)) :=
  ((embeddedSptFixedPointLeftParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁).reverse.trans
    (normalizedBondFixedPointGappedPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁)).trans
      (embeddedSptFixedPointRightParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁)

end MPSTensor
