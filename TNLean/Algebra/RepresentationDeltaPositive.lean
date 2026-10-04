/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RepresentationDeltaInverse
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Positivity of the weighted trace operator

For a unitary representation, the character projectors onto its occurring
isotypic summands are orthogonal projections. The source's operator \(\Delta\)
therefore is a positive linear map. Its explicit inverse shows that its matrix
in every orthonormal basis is positive definite.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 4.4,
equation `eq:noninj:deltadef`, `Papers/1001.3807/paper_v3.tex`, lines 970–976.
Unitarity is expressed by the adjoint identity for each group operator. Unlike
algebraic invertibility, positivity refers to this given inner product.
-/

open Module LinearMap
open scoped BigOperators ComplexOrder

namespace LinearMap
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Trace commutes with taking adjoints and complex conjugates.
Auxiliary to SCP10, charge detection, lines 2464–2486. -/
theorem trace_adjoint (A : Module.End ℂ E) :
    LinearMap.trace ℂ E A.adjoint = star (LinearMap.trace ℂ E A) := by
  let b := stdOrthonormalBasis ℂ E
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis,
    LinearMap.toMatrix_adjoint b b, Matrix.trace_conjTranspose,
    ← LinearMap.trace_eq_matrix_trace ℂ b.toBasis]

end LinearMap

namespace Representation
variable {G E : Type*} [Group G] [Fintype G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Fintype G] in
/-- Inversion conjugates the character of a unitary representation.
Auxiliary to SCP10, charge detection, lines 2464–2486. -/
theorem character_inv_of_unitary (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹) (g : G) :
    ρ.character g⁻¹ = star (ρ.character g) := by
  rw [character, ← hρ, LinearMap.trace_adjoint]
  rfl

omit [Fintype G] in
/-- Invariant subrepresentations of a unitary representation inherit its adjoint identity.
Source: the orthogonal isotypic decomposition in SCP10, Lemma 4.4, lines 970–976. -/
theorem adjoint_subrepresentation_of_unitary (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹) (S : Subrepresentation ρ) (g : G) :
    LinearMap.adjoint (S.toRepresentation g) = S.toRepresentation g⁻¹ := by
  rw [eq_comm]
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (ρ g⁻¹ (x : E)) (y : E) = inner ℂ (x : E) (ρ g (y : E))
  rw [← hρ, LinearMap.adjoint_inner_left]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- For unitary representations, the irreducible character projector is self-adjoint.
Source: the orthogonal isotypic decomposition in SCP10, Lemma 4.4, lines 970–976. -/
theorem charProjector_adjoint_of_unitary (ρ : Representation ℂ G E)
    (σ : Representation ℂ G F) (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) :
    LinearMap.adjoint (charProjector ρ σ.character) = charProjector ρ σ.character := by
  simp only [charProjector, map_smulₛₗ LinearMap.adjoint, map_sum, char_one,
    map_div₀, map_natCast, hρ]
  congr 1
  apply Fintype.sum_equiv (Equiv.inv G)
  intro g
  simp only [Equiv.inv_apply, inv_inv]
  change star (σ.character g⁻¹) • ρ g⁻¹ = _
  rw [character_inv_of_unitary σ hσ g, star_star]

/-- An irreducible character projector between unitary representations is positive.
Source: the orthogonal isotypic decomposition in SCP10, Lemma 4.4, lines 970–976. -/
theorem isPositive_charProjector_of_unitary (ρ : Representation ℂ G E)
    (σ : Representation ℂ G F) [σ.IsIrreducible]
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) :
    (charProjector ρ σ.character).IsPositive := by
  have h := LinearMap.isPositive_self_comp_adjoint (charProjector ρ σ.character)
  rw [charProjector_adjoint_of_unitary ρ σ hρ hσ, ← Module.End.mul_eq_comp,
    charProjector_mul_self] at h
  exact h

/-- A nonnegative weighted sum of occurring character projectors is positive for a
unitary representation. Source: the orthogonal block calculus of SCP10, Lemma 4.4,
lines 970–976, also used for the fourth-root weights in §7, lines 3000–3006. -/
theorem isPositive_sum_smul_charProjector_of_nonneg (ρ : Representation ℂ G E)
    (f : (G → ℂ) → ℂ) (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    (hf : ∀ χ ∈ irreducibleCharacterFinset ρ, 0 ≤ f χ) :
    (∑ χ ∈ irreducibleCharacterFinset ρ, f χ • charProjector ρ χ).IsPositive := by
  classical
  apply LinearMap.isPositive_sum
  intro χ hχ
  obtain ⟨S, hS, rfl⟩ := (mem_irreducibleCharacterFinset ρ).mp hχ
  exact (isPositive_charProjector_of_unitary ρ S.toRepresentation hρ
    (adjoint_subrepresentation_of_unitary ρ hρ S)).smul_of_nonneg (hf _ hχ)

/-- The weighted trace operator of a unitary finite-group representation is positive.
Source: the positive block coefficients of SCP10, Lemma 4.4, lines 970–976. -/
theorem isPositive_deltaOperator_of_unitary (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹) :
    (deltaOperator ρ).IsPositive := by
  classical
  rw [deltaOperator]
  apply LinearMap.IsPositive.smul_of_nonneg
  · apply isPositive_sum_smul_charProjector_of_nonneg ρ _ hρ
    intro χ hχ
    obtain ⟨S, hS, rfl⟩ := (mem_irreducibleCharacterFinset ρ).mp hχ
    rw [char_one, characterMultiplicity_eq_finrank]
    positivity
  · positivity
/-- In every orthonormal basis, the weighted trace operator is positive definite.
Source: SCP10, Lemma 4.4, lines 970–976; each occurring coefficient is positive. -/
theorem posDef_toMatrix_deltaOperator_of_unitary (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) :
    (LinearMap.toMatrix b.toBasis b.toBasis (deltaOperator ρ)).PosDef := by
  have hp := (LinearMap.posSemidef_toMatrix_iff b).mpr
    (isPositive_deltaOperator_of_unitary ρ hρ)
  apply hp.posDef_iff_isUnit.mpr
  exact (isUnit_deltaOperator ρ).map (LinearMap.toMatrixAlgEquiv b.toBasis).toMonoidHom

end Representation
