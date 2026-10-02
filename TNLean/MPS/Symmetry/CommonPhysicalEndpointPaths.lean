/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryGeneralLinearInverse
import TNLean.MPS.Symmetry.CommonPhysicalEndpoints
import TNLean.MPS.Symmetry.PhysicalMatrixBondCovariance

/-!
# Polar parent paths in the common physical representation

Each injective tensor is joined to its prescribed matrix-unit endpoint in
one common physical space. The paths use the actual polar-selected physical
isometries, including the original physical complements, and the common
representation determined by the two virtual actions and original on-site
representations.

**Scope restriction (one-site injective tensors and trivial character):**
These paths concern the single-block, one-site injective case of
arXiv:1010.3732, Sections II.C and II.F.2, equation eq:1d-sym:jointsym.
The several-block and scalar-character restrictions are documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex` and
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix
namespace MPSTensor

/-- An equal initial matrix gives the same interaction family and the same gap. -/
private def replaceInitialInteraction
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ h₀' : MPOTensor.ChainOperator d 2}
    (P : SymmetricGappedInteractionPath U h₀ h₁) (h : h₀ = h₀') :
    SymmetricGappedInteractionPath U h₀' h₁ where
  interaction := P.interaction
  interaction_zero := P.interaction_zero.trans h
  interaction_one := P.interaction_one
  hermitian := P.hermitian
  norm_le_one := P.norm_le_one
  continuous := P.continuous
  gap := P.gap
  symmetric := P.symmetric

/-- The first embedded original parent is joined to its prescribed fixed
point by a symmetric uniformly gapped path in the actual common physical
representation. Source context: arXiv:1010.3732, Sections II.C and II.F.2,
equation eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalLeftPolarGappedPath
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A : MPSTensor d₀ D₀) (hA : Kraus.IsInjective A)
    (hCov : ∀ g, rotatePhysical (U₀ g) A =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ) :
    SymmetricGappedInteractionPath (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁)
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (embeddedSptFixedPointLeft D₀ D₁)) 2))
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) A) 2)) := by
  have hMatrix (g : G) :
      (U₀ g : Matrix (Fin d₀) (Fin d₀) ℂ) * physicalMatrix A =
        physicalMatrix A * sptKron (sptGauge ρ₀ g) := by
    exact physicalMatrix_mul_eq_sptKron_of_unitary_covariance A (U₀ g) (sptGauge ρ₀ g)
      (h₀ g⁻¹) (hCov g)
  let X : G → Matrix.unitaryGroup (Fin D₀) ℂ :=
    fun g => ⟨sptGauge ρ₀ g, h₀ g⁻¹⟩
  have hp := embeddedPolarGappedInteractionPath U₀
    (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁) (commonPhysicalEmbeddingLeft d₁ D₁ A)
    (commonPhysicalEmbeddingLeft_isometry d₁ D₁ hA)
    (fun g => commonPhysicalEmbeddingLeft_intertwiner ρ₀ ρ₁ h₀ h₁ U₀ U₁ hA g (hMatrix g))
    A hA X hCov
  exact replaceInitialInteraction hp
    (congrArg LinearMap.toMatrix'
      (parentInteraction_commonPhysicalEmbeddingLeft_polar_endpoint d₁ D₁ hA 2))

/-- The second embedded original parent is joined to its prescribed fixed
point by a symmetric uniformly gapped path in the actual common physical
representation. Source context: arXiv:1010.3732, Sections II.C and II.F.2,
equation eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalRightPolarGappedPath
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A : MPSTensor d₁ D₁) (hA : Kraus.IsInjective A)
    (hCov : ∀ g, rotatePhysical (U₁ g) A =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ) :
    SymmetricGappedInteractionPath (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁)
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (embeddedSptFixedPointRight D₀ D₁)) 2))
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) A) 2)) := by
  have hMatrix (g : G) :
      (U₁ g : Matrix (Fin d₁) (Fin d₁) ℂ) * physicalMatrix A =
        physicalMatrix A * sptKron (sptGauge ρ₁ g) := by
    exact physicalMatrix_mul_eq_sptKron_of_unitary_covariance A (U₁ g) (sptGauge ρ₁ g)
      (h₁ g⁻¹) (hCov g)
  let X : G → Matrix.unitaryGroup (Fin D₁) ℂ :=
    fun g => ⟨sptGauge ρ₁ g, h₁ g⁻¹⟩
  have hp := embeddedPolarGappedInteractionPath U₁
    (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁) (commonPhysicalEmbeddingRight d₀ D₀ A)
    (commonPhysicalEmbeddingRight_isometry d₀ D₀ hA)
    (fun g => commonPhysicalEmbeddingRight_intertwiner ρ₀ ρ₁ h₀ h₁ U₀ U₁ hA g (hMatrix g))
    A hA X hCov
  exact replaceInitialInteraction hp
    (congrArg LinearMap.toMatrix'
      (parentInteraction_commonPhysicalEmbeddingRight_polar_endpoint d₀ D₀ hA 2))

end MPSTensor
