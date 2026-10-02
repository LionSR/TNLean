/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology
import TNLean.Algebra.CircleCohomology
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Rephasing virtual projective representations

In the equality-of-phases construction of Schuch, Pérez-García, and Cirac,
Section II.F.2 (arXiv:1010.3732, lines 886–929), virtual actions whose factor
systems have the same cohomology class are rephased to have a common factor
system. The following results establish this algebraic step for the concrete
matrix-valued projective representations used in TNLean.
-/

open scoped Matrix

namespace TNLean.Algebra

variable {G : Type} [Group G] {D : ℕ}

/-- Multiplying each virtual matrix by a scalar unit changes its factor system
by the corresponding coboundary. Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.2, lines 886–929. -/
def ProjectiveRepresentation.rephase {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω) (φ : G → Units ℂ) :
    ProjectiveRepresentation (D := D)
      (fun g h => φ g * φ h * (φ (g * h))⁻¹ * ω g h) where
  X g := Matrix.GeneralLinearGroup.scalar (Fin D) (φ g) * ρ.X g
  map_mul' := by
    intro g h
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Units.val_mul,
      Units.val_inv_eq_inv_val]
    calc
      ((φ g : ℂ) • (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) *
          ((φ h : ℂ) • (ρ.X h : Matrix (Fin D) (Fin D) ℂ))
          = ((φ g : ℂ) * (φ h : ℂ)) •
              ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
                (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) := by
              simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
      _ = ((φ g : ℂ) * (φ h : ℂ) * (φ (g * h) : ℂ)⁻¹ * (ω g h : ℂ)) •
          ((φ (g * h) : ℂ) •
            (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ)) := by
          rw [ρ.map_mul]
          simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]

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

/-- Rephasing by unit-circle scalars preserves virtual unitarity.
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
lines 886–921. -/
theorem ProjectiveRepresentation.rephase_mem_unitaryGroup
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
    (circleScalar_mem_unitaryGroup (φ g)) hρ

/-- Two unitary virtual actions with cohomologous circle-valued factor
systems can be aligned to an identical factor system without losing
unitarity. This is the rephasing prerequisite for the common-factor direct
sum in Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
lines 886–921. -/
theorem ProjectiveRepresentation.exists_unitary_rephase_of_cohomologous
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀.circlePhaseInclusion)
    (h : ω₁.CohomologousTo ω₀)
    (hρ₀ : ∀ g, (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ) :
    ∃ (ρ₁ : ProjectiveRepresentation (D := D) ω₁.circlePhaseInclusion)
      (φ : G → Circle),
      (∀ g, (ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) ∈
        Matrix.unitaryGroup (Fin D) ℂ) ∧
      (∀ g, ρ₁.X g = Matrix.GeneralLinearGroup.scalar (Fin D)
        (Circle.toUnits (φ g)) * ρ₀.X g) := by
  obtain ⟨φ, hφ⟩ := h
  let ψ : G → Circle := fun g => Complex.unitsPhase (φ g)
  have hphase : ∀ g k,
      ω₁.circlePhaseInclusion g k =
        Circle.toUnits (ψ g) * Circle.toUnits (ψ k) *
          (Circle.toUnits (ψ (g * k)))⁻¹ * ω₀.circlePhaseInclusion g k := by
    intro g k
    have hc := congrArg Complex.unitsPhase (hφ g k)
    simp only [Complex.unitsPhase.map_mul, Complex.unitsPhase.map_inv] at hc
    have hu := congrArg Circle.toUnits hc
    simpa only [ScalarCocycle.circlePhaseInclusion, ScalarCocycle.circlePhase,
      ψ, Circle.toUnits.map_mul, Circle.toUnits.map_inv] using hu
  have heq : (fun g k => Circle.toUnits (ψ g) * Circle.toUnits (ψ k) *
      (Circle.toUnits (ψ (g * k)))⁻¹ * ω₀.circlePhaseInclusion g k) =
      ω₁.circlePhaseInclusion := by
    funext g k
    exact (hphase g k).symm
  rw [← heq]
  refine ⟨ρ₀.rephase (fun g => Circle.toUnits (ψ g)), ψ, ?_, ?_⟩
  · intro g
    exact ρ₀.rephase_mem_unitaryGroup ψ g (hρ₀ g)
  · intro g
    rfl

end TNLean.Algebra
