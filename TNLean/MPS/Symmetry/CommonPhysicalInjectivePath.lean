/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.CommonPhysicalEndpointPaths
import TNLean.MPS.Symmetry.CommonPhysicalFixedPointPath
import TNLean.MPS.Symmetry.GappedInteractionPathComposition
import TNLean.MPS.Symmetry.UnitModulusProjectiveFactor

/-!
# A common physical path between injective parent Hamiltonians

Two injective tensors whose unitary virtual actions have the same factor
system are included isometrically into one physical representation.
Reversing the first polar deformation, following the enlarged fixed-point
interpolation, and following the second polar deformation joins their
canonical parent Hamiltonians by a symmetric uniformly gapped path.

Source: arXiv:1010.3732, Sections II.C and II.F.2,
equation eq:1d-sym:jointsym.

**Scope restriction (one-site injective tensors and trivial character):**
The construction concerns the single-block, one-site injective case with
trivial scalar character. These restrictions are documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex` and
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix

namespace MPSTensor

/-- The actual isometric images of two injective parent Hamiltonians are
joined by a symmetric uniformly gapped path when their unitary virtual
actions have the same factor system. The original tensor covariances
determine all physical intertwiners used in the construction.
Source: arXiv:1010.3732, Sections II.C and II.F.2,
equation eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalInjectiveGappedPath
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A₀ : MPSTensor d₀ D₀) (hA₀ : Kraus.IsInjective A₀)
    (A₁ : MPSTensor d₁ D₁) (hA₁ : Kraus.IsInjective A₁)
    (hCov₀ : ∀ g, rotatePhysical (U₀ g) A₀ =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ)
    (hCov₁ : ∀ g, rotatePhysical (U₁ g) A₁ =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ) :
    SymmetricGappedInteractionPath (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁)
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) 2))
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) 2)) :=
  ((commonPhysicalLeftPolarGappedPath
    ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ hCov₀).reverse.trans
    (commonPhysicalCanonicalFixedPointGappedPath ρ₀ ρ₁
      (NeZero.pos D₀) (NeZero.pos D₁) h₀ h₁ U₀ U₁)).trans
        (commonPhysicalRightPolarGappedPath ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₁ hA₁ hCov₁)

/-- Multiplication of a virtual action by unit-circle scalars preserves
the adjoint covariance of the original tensor.
Source: arXiv:1010.3732, Section II.F.2, lines 886--921. -/
theorem rotatePhysical_covariance_of_circle_rephase
    {G : Type} [Group G] {d D : ℕ}
    {ω η : TNLean.Algebra.ScalarCocycle G}
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω)
    (σ : TNLean.Algebra.ProjectiveRepresentation (D := D) η)
    (φ : G → Circle)
    (hX : ∀ g, σ.X g = Matrix.GeneralLinearGroup.scalar (Fin D)
      (Circle.toUnits (φ g)) * ρ.X g)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (A : MPSTensor d D)
    (hCov : ∀ g, rotatePhysical (U g) A =
      fun i => (sptGauge ρ g : Matrix (Fin D) (Fin D) ℂ) * A i *
        (sptGauge ρ g : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    ∀ g, rotatePhysical (U g) A =
      fun i => (sptGauge σ g : Matrix (Fin D) (Fin D) ℂ) * A i *
        (sptGauge σ g : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  have hMatrix (g : G) : (σ.X g : Matrix (Fin D) (Fin D) ℂ) =
      (φ g : ℂ) • (ρ.X g : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hX g]
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Circle.toUnits_apply, Units.val_mk0]
  simp only [hCov, sptGauge, hMatrix, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def,
    Complex.conj_mul', Circle.norm_coe, Complex.ofReal_one, one_pow, one_smul, forall_const]

/-- Cohomologous unitary virtual factors give a symmetric uniformly gapped
path between the actual common physical images of the original injective
parent Hamiltonians. Unit-circle rephasing preserves their original
adjoint covariances.
Source: arXiv:1010.3732, Section II.F.2, lines 886--929. -/
theorem exists_commonPhysicalInjectiveGappedPath_of_cohomologous
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω₀ ω₁ : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A₀ : MPSTensor d₀ D₀) (hA₀ : Kraus.IsInjective A₀)
    (A₁ : MPSTensor d₁ D₁) (hA₁ : Kraus.IsInjective A₁)
    (hCov₀ : ∀ g, rotatePhysical (U₀ g) A₀ =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ)
    (hCov₁ : ∀ g, rotatePhysical (U₁ g) A₁ =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ)
    (hCoh : ω₁.CohomologousTo ω₀) :
    ∃ V : G →* Matrix.unitaryGroup
        (Fin (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁)) ℂ,
      Nonempty (SymmetricGappedInteractionPath V
        (LinearMap.toMatrix' (parentInteraction
          (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) 2))
        (LinearMap.toMatrix' (parentInteraction
          (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) 2))) := by
  obtain ⟨σ, φ, hσ, hX⟩ :=
    ρ₀.exists_unitary_rephase_of_unitary_cohomologous ρ₁ h₀ h₁ hCoh
  have hCovσ := rotatePhysical_covariance_of_circle_rephase
    ρ₁ σ φ hX U₁ A₁ hCov₁
  exact ⟨commonSptPhysicalAction ρ₀ σ h₀ hσ U₀ U₁,
    ⟨commonPhysicalInjectiveGappedPath ρ₀ σ h₀ hσ U₀ U₁
      A₀ hA₀ A₁ hA₁ hCov₀ hCovσ⟩⟩

end MPSTensor
