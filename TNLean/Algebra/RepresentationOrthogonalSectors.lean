/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RepresentationDeltaPositive

/-!
# Orthogonality of irreducible sectors with distinct characters

In a unitary representation, invariant irreducible subspaces with distinct
characters are orthogonal. The character projector associated with the first
subspace is self-adjoint, acts as the identity on that subspace, and vanishes
on the second. This gives the orthogonal-family hypothesis needed to assemble
orthonormal sector bases into a global orthonormal basis.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the unitary isotypic
block decomposition in Lemma 4.4, local source lines 970–976, and the
multiplicity-one decomposition in Section 7, lines 2954–2972.
-/

namespace Representation
variable {G E : Type*} [Group G] [Finite G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Invariant irreducible subspaces of a unitary representation with distinct
characters are orthogonal. Source: SCP10, Lemma 4.4, lines 970–976. -/
theorem isOrtho_subrepresentation_of_character_ne (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    (S T : Subrepresentation ρ)
    [S.toRepresentation.IsIrreducible] [T.toRepresentation.IsIrreducible]
    (hne : S.toRepresentation.character ≠ T.toRepresentation.character) :
    S.toSubmodule ⟂ T.toSubmodule := by
  classical
  let : Fintype G := Fintype.ofFinite G
  apply Submodule.isOrtho_iff_inner_eq.mpr
  intro x hx y hy
  let P := charProjector ρ S.toRepresentation.character
  have hP : LinearMap.adjoint P = P :=
    charProjector_adjoint_of_unitary ρ S.toRepresentation hρ
      (fun g => adjoint_subrepresentation_of_unitary ρ hρ S g)
  have hxP : P x = x := by
    simpa only [P, ↓reduceIte] using
      charProjector_apply_of_mem ρ S.toRepresentation S hx
  have hyP : P y = 0 := by
    simpa only [P, Ne.symm hne, ↓reduceIte] using
      charProjector_apply_of_mem ρ S.toRepresentation T hy
  calc
    inner ℂ x y = inner ℂ (LinearMap.adjoint P x) y := by rw [hP, hxP]
    _ = inner ℂ x (P y) := LinearMap.adjoint_inner_left P y x
    _ = 0 := by rw [hyP, inner_zero_right]

/-- A family of invariant irreducible subspaces with pairwise distinct
characters is an orthogonal family in a unitary representation. Source:
SCP10, the multiplicity-one unitary decomposition in Section 7, lines 2954–2972. -/
theorem orthogonalFamily_subrepresentation_of_character_injective
    {I : Type*} (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    (S : I → Subrepresentation ρ) (hS : ∀ i, (S i).toRepresentation.IsIrreducible)
    (hχ : Function.Injective (fun i => (S i).toRepresentation.character)) :
    OrthogonalFamily ℂ (fun i => (S i).toSubmodule)
      (fun i => (S i).toSubmodule.subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro i j hij
  let := hS i
  let := hS j
  exact isOrtho_subrepresentation_of_character_ne ρ hρ (S i) (S j)
    (fun h => hij (hχ h))

end Representation
