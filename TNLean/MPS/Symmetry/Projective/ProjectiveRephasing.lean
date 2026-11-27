/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Cohomology.CocycleCohomology
import QICLean.Analysis.Cohomology.CircleCohomology
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Analysis.Cohomology.ProjectiveUnitary
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Rephasing virtual projective representations

In the equality-of-phases construction of Schuch, Pérez-García, and Cirac,
Section II.F.2 (arXiv:1010.3732, lines 886–929), virtual actions whose factor
systems have the same cohomology class are rephased to have a common factor
system. The following results establish this algebraic step for the concrete
matrix-valued projective representations used in TNLean.
-/

open scoped Matrix ScalarCohomology

variable {G : Type} [Group G] {D : ℕ}

namespace TNLean.Algebra

/-- A scalar matrix with coefficient in the unit circle is unitary. -/
theorem circleScalar_mem_unitaryGroup {D : ℕ} (z : Circle) :
    (Matrix.GeneralLinearGroup.scalar (Fin D) (Circle.toUnits z) :
      Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  simp only [Circle.toUnits_apply, Units.val_mk0, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Pi.star_apply, RCLike.star_def,
    Matrix.diagonal_eq_one]
  ext i
  change (z : ℂ) * star (z : ℂ) = 1
  rw [Complex.star_def, Complex.mul_conj']
  simp [Circle.norm_coe]

end TNLean.Algebra

/-- Rephasing by unit-circle scalars preserves virtual unitarity.
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
lines 886–921. -/
theorem TNLean.Algebra.rephase_mem_unitaryGroup
    {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (φ : G → Circle) (g : G)
    (hρ : (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    ((ρ.rephase (fun g => Circle.toUnits (φ g))).X g :
      Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  change ((Matrix.GeneralLinearGroup.scalar (Fin D) (Circle.toUnits (φ g)) :
      Matrix (Fin D) (Fin D) ℂ) *
      (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) ∈ _
  exact (Matrix.unitaryGroup (Fin D) ℂ).mul_mem
    (TNLean.Algebra.circleScalar_mem_unitaryGroup (φ g)) hρ

/-- Two unitary virtual actions with cohomologous circle-valued factor
systems can be aligned to an identical factor system without losing
unitarity. This is the rephasing prerequisite for the common-factor direct
sum in Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
lines 886–921. -/
theorem TNLean.Algebra.exists_unitary_rephase_of_cohomologous
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀.circlePhaseInclusion)
    (h : groupCohomology.IsMulCoboundary₂ (ω₁ / ω₀))
    (hρ₀ : ∀ g, (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ) :
    ∃ (ρ₁ : ProjectiveRepresentation (D := D) ω₁.circlePhaseInclusion)
      (φ : G → Circle),
      (∀ g, (ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) ∈
        Matrix.unitaryGroup (Fin D) ℂ) ∧
      (∀ g, ρ₁.X g = Matrix.GeneralLinearGroup.scalar (Fin D)
        (Circle.toUnits (φ g)) * ρ₀.X g) := by
  obtain ⟨φ, hφ⟩ := (ScalarCohomology.isMulCoboundary₂_div_iff _ _).mp h
  let ψ : G → Circle := fun g => Complex.unitsPhase (φ g)
  have hphase : ∀ g k,
      ω₁.circlePhaseInclusion (g, k) =
        Circle.toUnits (ψ g) * Circle.toUnits (ψ k) *
          (Circle.toUnits (ψ (g * k)))⁻¹ * ω₀.circlePhaseInclusion (g, k) := by
    intro g k
    have hc := congrArg Complex.unitsPhase (hφ g k)
    simp only [Complex.unitsPhase.map_mul, Complex.unitsPhase.map_inv] at hc
    have hu := congrArg Circle.toUnits hc
    simpa only [ScalarCocycle.circlePhaseInclusion, ScalarCocycle.circlePhase,
      ψ, Circle.toUnits.map_mul, Circle.toUnits.map_inv] using hu
  have heq : (fun p : G × G => Circle.toUnits (ψ p.1) * Circle.toUnits (ψ p.2) *
      (Circle.toUnits (ψ (p.1 * p.2)))⁻¹ * ω₀.circlePhaseInclusion p) =
      ω₁.circlePhaseInclusion := by
    funext ⟨g, k⟩
    exact (hphase g k).symm
  rw [← heq]
  refine ⟨ρ₀.rephase (fun g => Circle.toUnits (ψ g)), ψ, ?_, ?_⟩
  · intro g
    exact TNLean.Algebra.rephase_mem_unitaryGroup ρ₀ ψ g (hρ₀ g)
  · intro g
    rfl

section

/-!
## Unit-modulus factors of unitary projective representations

A unitary projective representation on a nonzero finite-dimensional space
has a unit-modulus factor system. Consequently its factor system agrees
with its pointwise circle-phase inclusion, so unit-circle rephasing applies
to the actual unitary virtual representatives.

The nonzero-dimension condition is essential: on the zero-dimensional
space the projective multiplication equation imposes no condition on the
scalar factor.
Source: arXiv:1010.3732, Section II.F.2, lines 886--921.
-/

open scoped Matrix Matrix.Norms.L2Operator ScalarCohomology

namespace ProjectiveRepresentation

variable {G : Type} [Group G] {D : ℕ} [NeZero D]
variable {ω : ScalarCocycle G}

/-- Two actual unitary projective representations with cohomologous
factors admit a common factor system after unit-circle rephasing.
Source: arXiv:1010.3732, Section II.F.2, lines 886--921. -/
theorem _root_.TNLean.MPS.Symmetry.exists_unitary_rephase_of_unitary_cohomologous
    {D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h : groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
        (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ (NeZero.pos D₁))) =
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
        (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀ (NeZero.pos D₀)))) :
    ∃ (σ : ProjectiveRepresentation (D := D₁) ω₀)
      (φ : G → Circle),
      (∀ g, (σ.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
      (∀ g, σ.X g = Matrix.GeneralLinearGroup.scalar (Fin D₁)
        (Circle.toUnits (φ g)) * ρ₁.X g) := by
  have e₀ := ρ₀.circlePhaseInclusion_eq_of_unitary h₀
  have e₁ := ρ₁.circlePhaseInclusion_eq_of_unitary h₁
  let τ : ProjectiveRepresentation (D := D₁) ω₁.circlePhaseInclusion :=
    { X := ρ₁.X
      map_mul' := fun g k => by simpa only [e₁] using ρ₁.map_mul g k }
  obtain ⟨σ, φ, hσ, hX⟩ := TNLean.Algebra.exists_unitary_rephase_of_cohomologous
    (ω₀ := ω₁) (ω₁ := ω₀) τ
      ((ScalarCohomology.H2π_eq_iff_isMulCoboundary₂_div _ _).mp h.symm) h₁
  exact ⟨{ X := σ.X
           map_mul' := fun g k => by simpa only [e₀] using σ.map_mul g k },
    φ, hσ, hX⟩

end ProjectiveRepresentation

end
