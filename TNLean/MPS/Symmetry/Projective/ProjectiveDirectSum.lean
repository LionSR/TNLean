/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Cohomology.ProjectiveRepresentation
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.Algebra.Unitary.MatrixCoordinateInclusion
import Mathlib.Data.Fin.Embedding

/-!
# Direct sums with a common projective factor system

The virtual direct sum in Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.2, equation `eq:1d-sym:jointsym`, is projective when its two
summands have the same factor system. This is the algebraic step following
rephasing and preceding the interpolation of the bond state.

## Inclusions of the virtual symmetry summands

The coordinate inclusions of the two bond summands intertwine their
projective representations with the common-factor direct sum.
Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`.
-/

section

open scoped Matrix

private def sumGL {D₀ D₁ : ℕ} (X : GL (Fin D₀) ℂ) (Y : GL (Fin D₁) ℂ) :
    GL (Fin D₀ ⊕ Fin D₁) ℂ where
  val := Matrix.fromBlocks X.val 0 0 Y.val
  inv := Matrix.fromBlocks X.inv 0 0 Y.inv
  val_inv := by
    simp [Matrix.fromBlocks_multiply]
  inv_val := by
    simp [Matrix.fromBlocks_multiply]

/-- The direct sum of two virtual representations with the same factor
system has that factor system. Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.F.2, equation `eq:1d-sym:jointsym`. -/
def ProjectiveRepresentation.directSum {G : Type} [Group G]
    {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) :
    ProjectiveRepresentation (D := D₀ + D₁) ω where
  X g := Units.map (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv).toMonoidHom
    (sumGL (ρ₀.X g) (ρ₁.X g))
  map_mul' g h := by
    change (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv) _ *
      (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv) _ =
      (ω (g, h) : ℂ) • (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv) _
    rw [← _root_.map_mul, ← map_smul]
    congr 1
    simp [sumGL, Matrix.fromBlocks_multiply, ρ₀.map_mul, ρ₁.map_mul,
      Matrix.fromBlocks_smul]

/-- The common-factor-system direct sum preserves unitarity. This supplies
the unitary virtual action in Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.2, equation `eq:1d-sym:jointsym`. -/
theorem ProjectiveRepresentation.directSum_mem_unitaryGroup
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G)
    (h₀ : (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ := by
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val) ∈ _
  apply Matrix.reindex_mem_unitaryGroup
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp h₀,
    Matrix.mem_unitaryGroup_iff.mp h₁]

end

section

open scoped Matrix

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

end
