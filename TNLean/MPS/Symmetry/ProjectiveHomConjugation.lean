/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.UnitModulusProjectiveFactor
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Conjugation on the space of projective intertwiners

For two unitary projective representations, the entrywise conjugate of the
first representation tensored with the second acts unitarily on the space
of intertwiners. The representatives may have different factor systems.
The resulting projective scalar cancels under matrix conjugation, so these
conjugations compose exactly. Neither normalized identity representatives
nor continuity of the representations is required.

Source context: arXiv:1010.3732, Section II.F.2, projective symmetry classes.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Kronecker

namespace TNLean.Algebra.ProjectiveRepresentation

variable {G : Type} [Group G] {D₀ D₁ : ℕ}
variable {ω₀ ω₁ : TNLean.Algebra.ScalarCocycle G}

/-- The factor of a unitary projective representation cancels with its
complex conjugate. The bond dimension must be nonzero. -/
theorem factor_mul_star_eq_one_of_unitary [NeZero D₀]
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) : (ω₀ g h : ℂ) * star (ω₀ g h : ℂ) = 1 := by
  change (ω₀ g h : ℂ) * (starRingEnd ℂ) (ω₀ g h : ℂ) = 1
  rw [Complex.mul_conj', ρ.norm_factor_eq_one_of_unitary hρ g h,
    Complex.ofReal_one, one_pow]

/-- The projective matrix acting on vectorized intertwiners. -/
def homMatrix
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁) (g : G) :
    Matrix (Fin D₀ × Fin D₁) (Fin D₀ × Fin D₁) ℂ :=
  (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ).map star ⊗ₖ
    (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ)

/-- The projective matrix on the intertwiner space is unitary. -/
theorem homMatrix_mem_unitaryGroup
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g : G) : homMatrix ρ₀ ρ₁ g ∈ Matrix.unitaryGroup _ ℂ :=
  Matrix.kronecker_mem_unitary (Matrix.map_star_mem_unitaryGroup_iff.mpr (h₀ g)) (h₁ g)

/-- The factor on the intertwiner space is the complex conjugate of the
first factor multiplied by the second. -/
theorem homMatrix_mul
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁) (g h : G) :
    homMatrix ρ₀ ρ₁ g * homMatrix ρ₀ ρ₁ h =
      (star (ω₀ g h : ℂ) * (ω₁ g h : ℂ)) • homMatrix ρ₀ ρ₁ (g * h) := by
  simp only [homMatrix]
  rw [← Matrix.mul_kronecker_mul]
  have hMap :
      (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ).map star *
        (ρ₀.X h : Matrix (Fin D₀) (Fin D₀) ℂ).map star =
      (((ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) *
        (ρ₀.X h : Matrix (Fin D₀) (Fin D₀) ℂ)).map star) := by
    exact (Matrix.map_mul (f := starRingEnd ℂ)).symm
  rw [hMap, ρ₀.map_mul, ρ₁.map_mul,
    Matrix.map_smulₛₗ star star _ (fun _ => star_smul _ _),
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]

private theorem homFactor_mul_star_eq_one [NeZero D₀] [NeZero D₁]
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) :
    (star (ω₀ g h : ℂ) * (ω₁ g h : ℂ)) *
      star (star (ω₀ g h : ℂ) * (ω₁ g h : ℂ)) = 1 := by
  simp only [star_mul, star_star]
  calc
    (star (ω₀ g h : ℂ) * (ω₁ g h : ℂ)) *
        (star (ω₁ g h : ℂ) * (ω₀ g h : ℂ)) =
        ((ω₀ g h : ℂ) * star (ω₀ g h : ℂ)) *
          ((ω₁ g h : ℂ) * star (ω₁ g h : ℂ)) := by ac_rfl
    _ = 1 := by
      rw [ρ₀.factor_mul_star_eq_one_of_unitary h₀,
        ρ₁.factor_mul_star_eq_one_of_unitary h₁, mul_one]

/-- Although the matrices on the intertwiner space are projective, their
conjugations compose exactly. -/
theorem homMatrix_conjugation_mul [NeZero D₀] [NeZero D₁]
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) (X : Matrix (Fin D₀ × Fin D₁) (Fin D₀ × Fin D₁) ℂ) :
    homMatrix ρ₀ ρ₁ g * (homMatrix ρ₀ ρ₁ h * X * (homMatrix ρ₀ ρ₁ h)ᴴ) *
        (homMatrix ρ₀ ρ₁ g)ᴴ =
      homMatrix ρ₀ ρ₁ (g * h) * X * (homMatrix ρ₀ ρ₁ (g * h))ᴴ := by
  calc
    homMatrix ρ₀ ρ₁ g * (homMatrix ρ₀ ρ₁ h * X * (homMatrix ρ₀ ρ₁ h)ᴴ) *
        (homMatrix ρ₀ ρ₁ g)ᴴ =
        (homMatrix ρ₀ ρ₁ g * homMatrix ρ₀ ρ₁ h) * X *
          (homMatrix ρ₀ ρ₁ g * homMatrix ρ₀ ρ₁ h)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = homMatrix ρ₀ ρ₁ (g * h) * X * (homMatrix ρ₀ ρ₁ (g * h))ᴴ := by
      rw [homMatrix_mul, Matrix.conjTranspose_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm, homFactor_mul_star_eq_one ρ₀ ρ₁ h₀ h₁ g h, one_smul]

end TNLean.Algebra.ProjectiveRepresentation
