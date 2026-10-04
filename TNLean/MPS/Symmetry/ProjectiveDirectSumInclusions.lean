/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixCoordinateInclusion
import TNLean.MPS.Symmetry.ProjectiveDirectSum
import Mathlib.Data.Fin.Embedding

/-!
# Inclusions of the virtual symmetry summands

The coordinate inclusions of the two bond summands intertwine their
projective representations with the common-factor direct sum.
Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`.
-/

open scoped Matrix

namespace TNLean.Algebra

/-- The first coordinate inclusion intertwines the projective direct sum
with its first summand. Source: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`. -/
theorem ProjectiveRepresentation.directSum_coordinateInclusion_left
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G) :
    ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) *
      Matrix.coordinateInclusion (Fin.castAddEmb D₁) =
    Matrix.coordinateInclusion (Fin.castAddEmb D₁) *
      (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) := by
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val) *
      Matrix.coordinateInclusion (Fin.castAddEmb D₁) =
    Matrix.coordinateInclusion (Fin.castAddEmb D₁) * (ρ₀.X g).val
  rw [Matrix.mul_coordinateInclusion]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [Matrix.coordinateInclusion, Matrix.mul_apply,
    Matrix.reindex_apply, Matrix.fromBlocks,
    ← finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right,
    finSumFinEquiv.injective.eq_iff]

/-- The second coordinate inclusion intertwines the projective direct sum
with its second summand. Source: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`. -/
theorem ProjectiveRepresentation.directSum_coordinateInclusion_right
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G) :
    ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) *
      Matrix.coordinateInclusion (Fin.natAddEmb D₀) =
    Matrix.coordinateInclusion (Fin.natAddEmb D₀) *
      (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) := by
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val) *
      Matrix.coordinateInclusion (Fin.natAddEmb D₀) =
    Matrix.coordinateInclusion (Fin.natAddEmb D₀) * (ρ₁.X g).val
  rw [Matrix.mul_coordinateInclusion]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [Matrix.coordinateInclusion, Matrix.mul_apply,
    Matrix.reindex_apply, Matrix.fromBlocks,
    ← finSumFinEquiv_apply_right, -finSumFinEquiv_apply_left,
    finSumFinEquiv.injective.eq_iff]

end TNLean.Algebra
