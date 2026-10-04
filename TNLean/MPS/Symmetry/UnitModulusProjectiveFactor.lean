/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import TNLean.MPS.Symmetry.ProjectiveRephasing

/-!
# Unit-modulus factors of unitary projective representations

A unitary projective representation on a nonzero finite-dimensional space
has a unit-modulus factor system. Consequently its factor system agrees
with its pointwise circle-phase inclusion, so unit-circle rephasing applies
to the actual unitary virtual representatives.

The nonzero-dimension condition is essential: on the zero-dimensional
space the projective multiplication equation imposes no condition on the
scalar factor.
Source: arXiv:1010.3732, Section II.F.2, lines 886--921.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace TNLean.Algebra.ProjectiveRepresentation

variable {G : Type} [Group G] {D : ℕ} [NeZero D]
variable {ω : TNLean.Algebra.ScalarCocycle G}

/-- The factor of a unitary projective representation has unit modulus.
Source: arXiv:1010.3732, Section II.F.2, lines 886--921. -/
theorem norm_factor_eq_one_of_unitary
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) : ‖(ω g h : ℂ)‖ = 1 := by
  have hnorm := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => ‖M‖) (ρ.map_mul g h)
  rw [CStarRing.norm_mem_unitary_mul _ (hρ g), CStarRing.norm_of_mem_unitary (hρ h),
    norm_smul, CStarRing.norm_of_mem_unitary (hρ (g * h)), mul_one] at hnorm
  exact hnorm.symm

/-- The circle-phase inclusion preserves the actual factor system of a
unitary projective representation.
Source: arXiv:1010.3732, Section II.F.2, lines 886--921. -/
theorem circlePhaseInclusion_eq_of_unitary
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ω.circlePhaseInclusion = ω := by
  funext g h
  apply Units.ext
  change (ω g h : ℂ) / ‖(ω g h : ℂ)‖ = (ω g h : ℂ)
  simp only [ρ.norm_factor_eq_one_of_unitary hρ g h, Complex.ofReal_one, div_one]

/-- Two actual unitary projective representations with cohomologous
factors admit a common factor system after unit-circle rephasing.
Source: arXiv:1010.3732, Section II.F.2, lines 886--921. -/
theorem exists_unitary_rephase_of_unitary_cohomologous
    {D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω₀ ω₁ : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h : ω₁.CohomologousTo ω₀) :
    ∃ (σ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₀)
      (φ : G → Circle),
      (∀ g, (σ.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
      (∀ g, σ.X g = Matrix.GeneralLinearGroup.scalar (Fin D₁)
        (Circle.toUnits (φ g)) * ρ₁.X g) := by
  have e₀ := ρ₀.circlePhaseInclusion_eq_of_unitary h₀
  have e₁ := ρ₁.circlePhaseInclusion_eq_of_unitary h₁
  let τ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁.circlePhaseInclusion :=
    { X := ρ₁.X
      map_mul' := fun g k => by simpa only [e₁] using ρ₁.map_mul g k }
  obtain ⟨σ, φ, hσ, hX⟩ := exists_unitary_rephase_of_cohomologous
    (ω₀ := ω₁) (ω₁ := ω₀) τ h.symm h₁
  exact ⟨{ X := σ.X
           map_mul' := fun g k => by simpa only [e₀] using σ.map_mul g k },
    φ, hσ, hX⟩

end TNLean.Algebra.ProjectiveRepresentation
