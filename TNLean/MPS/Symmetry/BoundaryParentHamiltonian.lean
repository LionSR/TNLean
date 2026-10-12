/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BoundaryParentCommutation
import TNLean.MPS.MPDO.BoundaryCut
import TNLean.MPS.ParentHamiltonian.MatrixRepresentation
import TNLean.MPS.ParentHamiltonian.NonzeroInteraction

/-!
# Periodic canonical parents for arbitrary-boundary MPO symmetries

If an MPO tensor is compatible with an MPS tensor and its entire boundary range
at the interaction length is adjoint-closed, each cyclic canonical parent term
commutes with every periodic MPO whose virtual boundary commutes with the tensor
letters. Hence the periodic parent Hamiltonian commutes as well. A strict local
dimension inequality guarantees that the canonical interaction is nonzero.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Section 5,
lines 1236--1320, and Appendix B, lines 2457--2466.

**Scope restriction (explicit adjoint closure):** the hypothesis concerns the
entire boundary range of the assembled tensor, not each labelled block. This
file does not construct a star-compatible weak-Hopf realization or integral.
For weak-Hopf averaging, E(I - P) = Q - E(P), with Q the represented coproduct
of the unit; the canonical ambient parent is I - P. The nonzero conclusion is
about this canonical parent, not the literal weak-Hopf average. Compatibility
alone does not imply QP = P. See `docs/paper-gaps/glm23_wha_parent_completion.tex`.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D₁ D₂ L N : ℕ} {T : MPOTensor d D₁} {A : MPSTensor d D₂}

/-- The matrix of the canonical local parent commutes with every boundary
operator under compatibility and adjoint closure of the whole boundary range.
Source: GLM23, arXiv:2203.12563v3, Section 5, lines 1276--1320. -/
theorem IsBoundaryCompatible.parentInteraction_matrix_commute_mpoWithBoundary
    (h : IsBoundaryCompatible T A) (hL : 0 < L)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) :
    Commute (LinearMap.toMatrix' (MPSTensor.parentInteraction A L))
      (mpoWithBoundary T X L) := by
  have hES := h.parentInteractionES_commute_mpoWithBoundary hL hstar X
  rw [MPSTensor.parentInteractionES_eq_toEuclideanLin_parentMatrix] at hES
  apply (commute_iff_eq _ _).2
  apply Matrix.toEuclideanLin.injective
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    Module.End.mul_eq_comp] using hES.eq

/-- Every cyclic translate, including a wrapping window, of the canonical local
parent commutes with each globally commuting-boundary MPO. Source: GLM23,
arXiv:2203.12563v3, Section 5, lines 1276--1320, with adjoint closure explicit. -/
theorem IsBoundaryCompatible.localTermES_commute_mpoWithBoundary
    (h : IsBoundaryCompatible T A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    (i : Fin N) {X : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hX : X ∈ commutingBoundaryAlgebra T) :
    Commute (MPSTensor.localTermES A L i)
      (Matrix.toEuclideanLin (mpoWithBoundary T X N)) := by
  rw [MPSTensor.localTermES_eq_toEuclideanLin_embedLocalOperator A hLN i]
  have hmat := embedLocalOperator_commute_mpoWithBoundary T hLN i
    (LinearMap.toMatrix' (MPSTensor.parentInteraction A L))
    (h.parentInteraction_matrix_commute_mpoWithBoundary hL hstar) hX
  apply (commute_iff_eq _ _).2
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    Module.End.mul_eq_comp] using congrArg Matrix.toEuclideanLin hmat.eq

/-- On every periodic chain at least as long as the interaction range, the
canonical parent Hamiltonian commutes with each globally commuting-boundary
MPO. Adjoint closure is required only at the local interaction length, for the
entire assembled boundary range. Source: GLM23, arXiv:2203.12563v3, Section 5,
lines 1276--1320; see the module's scope restriction. -/
theorem IsBoundaryCompatible.parentHamiltonianES_commute_mpoWithBoundary
    (h : IsBoundaryCompatible T A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    {X : Matrix (Fin D₁) (Fin D₁) ℂ} (hX : X ∈ commutingBoundaryAlgebra T) :
    Commute (MPSTensor.parentHamiltonianES A L N)
      (Matrix.toEuclideanLin (mpoWithBoundary T X N)) := by
  rw [MPSTensor.parentHamiltonianES_eq_sum_localTermES]
  apply (commute_iff_eq _ _).2
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    (h.localTermES_commute_mpoWithBoundary hL hLN hstar i hX).eq

/-- The periodic commutation conclusion in the original function-space
coordinates. Source: GLM23, arXiv:2203.12563v3, Section 5, lines 1276--1320,
under compatibility and explicit adjoint closure of the whole boundary range. -/
theorem IsBoundaryCompatible.parentHamiltonian_commute_mpoWithBoundary
    (h : IsBoundaryCompatible T A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    {X : Matrix (Fin D₁) (Fin D₁) ℂ} (hX : X ∈ commutingBoundaryAlgebra T) :
    Commute (MPSTensor.parentHamiltonian A L N)
      (Matrix.toLin' (mpoWithBoundary T X N)) := by
  unfold MPSTensor.parentHamiltonian
  apply (commute_iff_eq _ _).2
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [MPSTensor.localTerm_eq_toLin'_embedLocalOperator A hLN i]
  have hmat := embedLocalOperator_commute_mpoWithBoundary T hLN i
    (LinearMap.toMatrix' (MPSTensor.parentInteraction A L))
    (h.parentInteraction_matrix_commute_mpoWithBoundary hL hstar) hX
  simpa only [Matrix.toLin'_mul, Module.End.mul_eq_comp] using
    congrArg Matrix.toLin' hmat.eq

/-- Compatibility with an adjoint-closed assembled boundary range produces a
nonzero canonical local interaction and a symmetric periodic parent Hamiltonian
whenever the local physical dimension exceeds the square of the state bond
dimension. Source: GLM23, arXiv:2203.12563v3, Section 5, lines 1276--1320.
This does not assert nonzeroness of the literal weak-Hopf-averaged interaction. -/
theorem IsBoundaryCompatible.nonzero_parentInteractionES_and_parentHamiltonianES_commute
    (h : IsBoundaryCompatible T A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    (hDim : d ^ L > D₂ ^ 2) :
    MPSTensor.parentInteractionES A L ≠ 0 ∧
      ∀ X ∈ commutingBoundaryAlgebra T,
        Commute (MPSTensor.parentHamiltonianES A L N)
          (Matrix.toEuclideanLin (mpoWithBoundary T X N)) := by
  exact ⟨MPSTensor.parentInteractionES_ne_zero A L hDim,
    fun _ hX ↦ h.parentHamiltonianES_commute_mpoWithBoundary hL hLN hstar hX⟩

end MPOTensor
