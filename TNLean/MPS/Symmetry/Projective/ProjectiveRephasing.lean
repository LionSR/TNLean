/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Cohomology.CocycleCohomology
import QICLean.Analysis.Cohomology.CircleCohomology
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Analysis.Cohomology.ProjectiveUnitary

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
