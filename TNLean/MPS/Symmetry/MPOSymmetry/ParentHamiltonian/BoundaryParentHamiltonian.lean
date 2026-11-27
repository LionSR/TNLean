/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.ParentHamiltonian.BoundaryParentCommutation
import TNLean.MPS.Operator.Boundary.BoundaryCut
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport
import TNLean.MPS.Operator.Boundary.BlockBoundarySelector
import TNLean.MPS.Operator.Boundary.DualRepresentationAdjointBoundary
import TNLean.MPS.Operator.Boundary.BlockSumAdjointBoundary

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

## Individual block symmetries of canonical parent Hamiltonians

A summand boundary selector commuting with every assembled tensor letter
isolates an individual periodic MPO block. The periodic canonical parent
therefore commutes with each labelled MPO under compatibility and adjoint
closure of the entire assembled
boundary range. Adjoint closure need not hold separately for each label.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Definition `defsym`,
lines 1236--1246, and Section 5, lines 1276--1320. The star-compatible weak-Hopf
realization remains separate; see `docs/paper-gaps/glm23_wha_parent_completion.tex`.

## Canonical parent symmetry from star-compatible dual representations

The star-compatible coalgebra representation supplies arbitrary-boundary
adjoint closure. Compatibility with an MPS therefore gives commutation of its
canonical local parent with every boundary operator, and commutation of its
periodic parent with boundaries in the tensor-letter centralizer.

The centralizer condition is retained for periodic windows that wrap around
the chain. No integral-averaging formula, reconstruction of a C*-weak Hopf
algebra, or realization of a given mixed tensor is asserted.

### References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Section 5, lines 1236--1320.
* Molnár et al., arXiv:2204.05940v1, Section 4 and Section 5.5.

## Canonical parent symmetry from normal periodic adjoint duality

Compatibility of an MPS with the actual unweighted MPO block sum implies
symmetry of its periodic canonical parent under every labelled periodic
operator when the normal positive-dimensional blocks possess an involutive
periodic physical adjoint dual. The entire arbitrary-boundary range is proved
adjoint closed from these hypotheses before applying the canonical-parent
commutation theorem.

### References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Definition `defsym`,
  Section 5, and Appendix B. This is a canonical-parent consequence with the
  physical star-representation hypothesis explicit. It does not construct a
  weak Hopf algebra or identify a weak-Hopf-averaged interaction.
-/

section

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
      (mpoWithBoundary T X L) :=
  MPSTensor.commute_toMatrix'_parentInteraction_of_starAlgebra_invariant A
    (StarAlgebra.adjoin ℂ (Set.range (fun Y ↦ mpoWithBoundary T Y L)))
    (h.groundSpaceES_invariant_boundaryStarAlgebra hL hstar)
    (StarAlgebra.subset_adjoin ℂ _ ⟨X, rfl⟩)

/-- The matrix of the canonical local parent commutes with every boundary
operator of a family of compatible operator tensors, when the union of their
boundary ranges is adjoint-closed. Source: GLM23, arXiv:2203.12563v3,
Section 5, lines 1276--1320. -/
theorem parentInteraction_matrix_commute_mpoWithBoundary_of_forall_isBoundaryCompatible
    {ι : Type*} {T : ι → MPOTensor d D₁} (h : ∀ i, IsBoundaryCompatible (T i) A)
    (hL : 0 < L)
    (hstar : ∀ i (X : Matrix (Fin D₁) (Fin D₁) ℂ), ∃ j, ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
      (mpoWithBoundary (T i) X L)ᴴ = mpoWithBoundary (T j) Y L)
    (i : ι) (X : Matrix (Fin D₁) (Fin D₁) ℂ) :
    Commute (LinearMap.toMatrix' (MPSTensor.parentInteraction A L))
      (mpoWithBoundary (T i) X L) := by
  refine MPSTensor.commute_toMatrix'_parentInteraction_of_conjTranspose_mem A
    {B | ∃ i X, mpoWithBoundary (T i) X L = B} ?_ ?_ ⟨i, X, rfl⟩
  · rintro B ⟨i, X, rfl⟩
    obtain ⟨j, Y, hY⟩ := hstar i X
    exact ⟨j, Y, hY.symm⟩
  · rintro B ⟨i, X, rfl⟩
    exact (h i).groundSpaceES_mem_invtSubmodule X hL

/-- Every cyclic translate, including a wrapping window, of the canonical local
parent commutes with each globally commuting-boundary MPO. Source: GLM23,
arXiv:2203.12563v3, Section 5, lines 1276--1320, with adjoint closure explicit. -/
theorem IsBoundaryCompatible.commute_parentRingInteraction_term_mpoWithBoundary
    (h : IsBoundaryCompatible T A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    (i : Fin N) {X : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hX : X ∈ commutingBoundaryAlgebra T) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute ((MPSTensor.parentRingInteraction A L N).term i) (mpoWithBoundary T X N) := by
  have : NeZero N := ⟨by omega⟩
  rw [ManyBody.Interaction.translationInvariant_term_of_le _ hLN i]
  exact placeAlong_ringWindow_commute_mpoWithBoundary T hLN i
    (LinearMap.toMatrix' (MPSTensor.parentInteraction A L))
    (h.parentInteraction_matrix_commute_mpoWithBoundary hL hstar) hX

/-- On every periodic chain at least as long as the interaction range, the
canonical parent Hamiltonian commutes with each globally commuting-boundary
MPO. Adjoint closure is required only at the local interaction length, for the
entire assembled boundary range. Source: GLM23, arXiv:2203.12563v3, Section 5,
lines 1276--1320; see the module's scope restriction. -/
theorem IsBoundaryCompatible.commute_hamiltonian_parentRingInteraction_mpoWithBoundary
    (h : IsBoundaryCompatible T A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    {X : Matrix (Fin D₁) (Fin D₁) ℂ} (hX : X ∈ commutingBoundaryAlgebra T) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (MPSTensor.parentRingInteraction A L N).hamiltonian (mpoWithBoundary T X N) :=
  haveI : NeZero N := ⟨by omega⟩
  Commute.sum_left _ _ _ fun i _ ↦
    h.commute_parentRingInteraction_term_mpoWithBoundary hL hLN hstar i hX

/-- Compatibility with an adjoint-closed assembled boundary range produces a
nonzero canonical local interaction and a symmetric periodic parent Hamiltonian
whenever the local physical dimension exceeds the square of the state bond
dimension. Source: GLM23, arXiv:2203.12563v3, Section 5, lines 1276--1320.
This does not assert nonzeroness of the literal weak-Hopf-averaged interaction. -/
theorem IsBoundaryCompatible.nonzero_parentInteraction_and_hamiltonian_parentRingInteraction_commute
    (h : IsBoundaryCompatible T A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    (hDim : d ^ L > D₂ ^ 2) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.toMatrix' (MPSTensor.parentInteraction A L) ≠ 0 ∧
      ∀ X ∈ commutingBoundaryAlgebra T,
        Commute (MPSTensor.parentRingInteraction A L N).hamiltonian (mpoWithBoundary T X N) :=
  haveI : NeZero N := ⟨by omega⟩
  ⟨MPSTensor.toMatrix'_parentInteraction_ne_zero A L hDim,
    fun _ hX ↦ h.commute_hamiltonian_parentRingInteraction_mpoWithBoundary hL hLN hstar hX⟩

end MPOTensor

end

section

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r D L N : ℕ} {dim : Fin r → ℕ}
    {O : (a : Fin r) → MPOTensor d (dim a)} {A : MPSTensor d D}

/-- Compatibility with the assembled MPO tensor and adjoint closure of its whole
local boundary range imply commutation of the periodic parent with every
individual periodic MPO block. Source: GLM23, arXiv:2203.12563v3, `defsym` and
Section 5, lines 1276--1320, with the assembled adjoint-closure hypothesis explicit. -/
theorem IsBoundaryCompatible.commute_hamiltonian_parentRingInteraction_mpo_block
    (h : IsBoundaryCompatible (blockSum O) A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin (∑ a : Fin r, dim a)) (Fin (∑ a : Fin r, dim a)) ℂ,
      ∃ Y : Matrix (Fin (∑ a : Fin r, dim a)) (Fin (∑ a : Fin r, dim a)) ℂ,
        (mpoWithBoundary (blockSum O) X L)ᴴ = mpoWithBoundary (blockSum O) Y L)
    (a : Fin r) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (MPSTensor.parentRingInteraction A L N).hamiltonian (mpo (O a) N) := by
  have : NeZero N := ⟨by omega⟩
  simpa only [mpoWithBoundary_blockSum_blockBoundarySelector] using
    h.commute_hamiltonian_parentRingInteraction_mpoWithBoundary hL hLN hstar
      (blockBoundarySelector_mem_commutingBoundaryAlgebra O a)

end MPOTensor

end

section

open scoped Matrix

namespace MPOTensor

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Coalgebra ℂ H]
  [StarAddMonoid H] [StarModule ℂ H]
variable {d D Dₐ L N : ℕ}

/-- The canonical local interaction commutes with every boundary operator of
a compatible star-coalgebra dual representation. Its adjoint closure is
derived from the representation, not supplied as a premise. -/
theorem IsBoundaryCompatible.commute_toMatrix'_parentInteraction_of_dualRepresentation
    (hcomul : ∀ x : H,
      Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x))
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible (ofDualRepresentation φ ψ) A)
    (hL : 0 < L) (X : Matrix (Fin D) (Fin D) ℂ) :
    Commute (LinearMap.toMatrix' (MPSTensor.parentInteraction A L))
      (mpoWithBoundary (ofDualRepresentation φ ψ) X L) := by
  apply h.parentInteraction_matrix_commute_mpoWithBoundary hL ?_ X
  intro Y
  obtain ⟨Z, hZ⟩ := exists_adjointBoundary_of_dualRepresentation hcomul φ hφ ψ hψ Y
  exact ⟨Z, hZ L⟩

/-- The periodic canonical parent commutes with every represented boundary
that commutes with the tensor letters. This includes wrapping interaction
windows and retains their necessary centralizer condition. -/
theorem IsBoundaryCompatible.commute_hamiltonian_parentRingInteraction_of_dualRepresentation
    (hcomul : ∀ x : H,
      Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x))
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible (ofDualRepresentation φ ψ) A)
    (hL : 0 < L) (hLN : L ≤ N) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ commutingBoundaryAlgebra (ofDualRepresentation φ ψ)) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (MPSTensor.parentRingInteraction A L N).hamiltonian
      (mpoWithBoundary (ofDualRepresentation φ ψ) X N) := by
  have : NeZero N := ⟨by omega⟩
  apply h.commute_hamiltonian_parentRingInteraction_mpoWithBoundary hL hLN ?_ hX
  intro Y
  obtain ⟨Z, hZ⟩ := exists_adjointBoundary_of_dualRepresentation hcomul φ hφ ψ hψ Y
  exact ⟨Z, hZ L⟩

end MPOTensor

end

section

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r D L N : ℕ} {dim : Fin r → ℕ}
    {O : (a : Fin r) → MPOTensor d (dim a)} {A : MPSTensor d D}
    {dual : Fin r → Fin r}

/-- Compatibility and normal periodic adjoint duality imply commutation of
the canonical parent with every periodic block. Adjoint closure of the whole
assembled boundary range is derived, rather than assumed. No normality or
injectivity hypothesis on the compatible state tensor is needed. -/
theorem IsBoundaryCompatible.commute_hamiltonian_parentRingInteraction_mpo_block_of_periodicAdjoint
    (h : IsBoundaryCompatible (blockSum O) A)
    (hAdjoint : IsPeriodicAdjointFamily O dual) (hdual : Function.Involutive dual)
    (hNormal : ∀ a, Kraus.IsNormal (O a).toMPSTensor)
    (hDim : ∀ a, 0 < dim a) (hL : 0 < L) (hLN : L ≤ N) (a : Fin r) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (MPSTensor.parentRingInteraction A L N).hamiltonian (mpo (O a) N) := by
  have : NeZero N := ⟨by omega⟩
  apply h.commute_hamiltonian_parentRingInteraction_mpo_block hL hLN ?_ a
  intro X
  obtain ⟨Y, hY⟩ := hAdjoint.isBoundaryAdjointClosed_blockSum hdual hNormal hDim X
  exact ⟨Y, hY L hL⟩

end MPOTensor

end
