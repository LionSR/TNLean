/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryClosedness
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import QICLean.Algebra.StarSubalgebraIsotypic

/-!
# Canonical local parents for star-closed arbitrary-boundary MPO symmetries

Length-independent arbitrary-boundary compatibility implies invariance of every
positive-length MPS ground space. If the corresponding boundary operators are
closed under conjugate transposition, the ground space is reducing, so its
canonical complementary orthogonal projection commutes with every boundary
operator. The generated star algebra includes the ambient identity even when the
original operator algebra has only a support projection as its unit.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `eq:compatible`,
lines 431--469, and the parent-Hamiltonian discussion at lines 1276--1320.

**Scope restriction (local symmetry):** adjoint closure is an explicit hypothesis
here. This file does not construct a weak Hopf algebra or its integral, identify
its boundary representation, or prove a full-chain tensor-cut formula. It proves
commutation of the canonical local parent without averaging the complementary
projection. In Appendix B, averaging the support projection and taking its
ambient complement must be distinguished from averaging the parent interaction:
if the averaging map sends the ambient identity to a proper support projection,
the two operations differ by its complementary projection. See the accompanying
`docs/paper-gaps/glm23_wha_parent_completion.tex` source review.
-/

open scoped Matrix

noncomputable section

/-- A subspace invariant under a conjugate-transpose-closed set is invariant
under the unital star algebra it generates. This allows a nonunital boundary
operator algebra to be used with the orthogonal-reduction theorem. -/
private theorem invariant_adjoin_of_conjTranspose_mem
    {n : Type*} [Fintype n] [DecidableEq n]
    (s : Set (Matrix n n ℂ)) (hs : ∀ B ∈ s, Bᴴ ∈ s)
    (q : Submodule ℂ (EuclideanSpace ℂ n))
    (hq : ∀ B ∈ s, q ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin B)) :
    (StarAlgebra.adjoin ℂ s).IsInvariantSubspace q := by
  intro B hB
  change B ∈ Algebra.adjoin ℂ (s ∪ star s) at hB
  induction hB using Algebra.adjoin_induction with
  | mem B hB =>
    rcases hB with hB | hB
    · exact hq B hB
    · have hBs : Bᴴ ∈ s := by
        simpa only [Matrix.star_eq_conjTranspose] using Set.mem_star.mp hB
      have hB' : B ∈ s := by
        simpa only [Matrix.conjTranspose_conjTranspose] using hs Bᴴ hBs
      exact hq B hB'
  | algebraMap c =>
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    change Matrix.toEuclideanLin (algebraMap ℂ (Matrix n n ℂ) c) x ∈ q
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLpLin_one]
    change c • x ∈ q
    exact q.smul_mem c hx
  | add B C hB hC ihB ihC =>
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at ihB ihC ⊢
    intro x hx
    change Matrix.toEuclideanLin (B + C) x ∈ q
    rw [map_add]
    change Matrix.toEuclideanLin B x + Matrix.toEuclideanLin C x ∈ q
    exact q.add_mem (ihB x hx) (ihC x hx)
  | mul B C hB hC ihB ihC =>
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at ihB ihC ⊢
    intro x hx
    change Matrix.toEuclideanLin (B * C) x ∈ q
    rw [Matrix.toLpLin_mul_same]
    exact ihB _ (ihC x hx)

namespace MPSTensor

/-- A star algebra preserving the local MPS support commutes with the
canonical local parent interaction. This is the orthogonal-reduction form
of the local symmetry assertion in GLM23, arXiv:2203.12563v3, lines 1276--1320;
it does not assert a weak-Hopf averaging formula. -/
theorem parentInteractionES_commute_of_starAlgebra_invariant
    {d D L : ℕ} (A : MPSTensor d D)
    (S : StarSubalgebra ℂ (Matrix (Cfg d L) (Cfg d L) ℂ))
    (hS : S.IsInvariantSubspace (groundSpaceES A L))
    {B : Matrix (Cfg d L) (Cfg d L) ℂ} (hB : B ∈ S) :
    Commute (parentInteractionES A L) (Matrix.toEuclideanLin B) := by
  apply LinearMap.ext
  intro x
  change (groundSpaceES A L)ᗮ.starProjection (Matrix.toEuclideanLin B x) =
    Matrix.toEuclideanLin B ((groundSpaceES A L)ᗮ.starProjection x)
  exact S.starProjection_toEuclideanLin_comm
    (fun C hC ↦ S.orthogonal_mem_invtSubmodule hS C hC) hB x

end MPSTensor

namespace MPOTensor

variable {d D₁ D₂ L : ℕ} {T : MPOTensor d D₁} {A : MPSTensor d D₂}

/-- Arbitrary-boundary compatibility preserves the Euclidean realization of
the local MPS ground space. Source: GLM23, arXiv:2203.12563v3,
`eq:compatible`, lines 431--469. -/
theorem IsBoundaryCompatible.groundSpaceES_mem_invtSubmodule
    (h : IsBoundaryCompatible T A) (X : Matrix (Fin D₁) (Fin D₁) ℂ)
    (hL : 0 < L) :
    MPSTensor.groundSpaceES A L ∈
      Module.End.invtSubmodule (Matrix.toEuclideanLin (mpoWithBoundary T X L)) := by
  intro x hx
  apply (MPSTensor.mem_groundSpaceES_iff A L _).mpr
  change mpoWithBoundary T X L *ᵥ
    ((WithLp.linearEquiv 2 ℂ (MPSTensor.NSiteSpace d L)) x) ∈
      MPSTensor.groundSpace A L
  exact h.mulVec_mem_groundSpace X hL
    ((MPSTensor.mem_groundSpaceES_iff A L x).mp hx)

/-- Under adjoint closure at the local length, boundary compatibility makes
the MPS ground space invariant under the generated unital star algebra.
The adjoined ambient identity causes no restriction on a weak-Hopf support
projection. Source: GLM23, `eq:compatible` and Appendix B; adjoint closure is
stated explicitly instead of assumed through an unformalized WHA interface. -/
theorem IsBoundaryCompatible.groundSpaceES_invariant_boundaryStarAlgebra
    (h : IsBoundaryCompatible T A) (hL : 0 < L)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L) :
    (StarAlgebra.adjoin ℂ (Set.range (fun X ↦ mpoWithBoundary T X L))).IsInvariantSubspace
      (MPSTensor.groundSpaceES A L) := by
  apply invariant_adjoin_of_conjTranspose_mem
  · rintro B ⟨X, rfl⟩
    obtain ⟨Y, hY⟩ := hstar X
    exact ⟨Y, hY.symm⟩
  · rintro B ⟨X, rfl⟩
    exact h.groundSpaceES_mem_invtSubmodule X hL

/-- Every arbitrary-boundary operator commutes with the canonical local
parent when the boundary range is adjoint-closed. Source: the local symmetry
conclusion in GLM23, arXiv:2203.12563v3, lines 1276--1320. This theorem uses
orthogonal reduction and makes no nonzeroness claim about averaging a parent
term by a nonunital weak-Hopf map. -/
theorem IsBoundaryCompatible.parentInteractionES_commute_mpoWithBoundary
    (h : IsBoundaryCompatible T A) (hL : 0 < L)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) :
    Commute (MPSTensor.parentInteractionES A L)
      (Matrix.toEuclideanLin (mpoWithBoundary T X L)) := by
  exact MPSTensor.parentInteractionES_commute_of_starAlgebra_invariant A
    (StarAlgebra.adjoin ℂ (Set.range (fun Y ↦ mpoWithBoundary T Y L)))
    (h.groundSpaceES_invariant_boundaryStarAlgebra hL hstar)
    (StarAlgebra.subset_adjoin ℂ _ ⟨X, rfl⟩)

/-- The local-parent commutation identity in the original function-space
coordinates. Source: GLM23, `eq:compatible` and lines 1276--1320, under the
explicit local adjoint-closure hypothesis. -/
theorem IsBoundaryCompatible.parentInteraction_mpoWithBoundary_mulVec
    (h : IsBoundaryCompatible T A) (hL : 0 < L)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) (x : MPSTensor.NSiteSpace d L) :
    MPSTensor.parentInteraction A L (mpoWithBoundary T X L *ᵥ x) =
      mpoWithBoundary T X L *ᵥ MPSTensor.parentInteraction A L x := by
  let e := WithLp.linearEquiv 2 ℂ (MPSTensor.NSiteSpace d L)
  have hh := LinearMap.congr_fun
    (h.parentInteractionES_commute_mpoWithBoundary hL hstar X).eq (e.symm x)
  change (MPSTensor.groundSpaceES A L)ᗮ.starProjection
      (Matrix.toEuclideanLin (mpoWithBoundary T X L) (e.symm x)) =
    Matrix.toEuclideanLin (mpoWithBoundary T X L)
      ((MPSTensor.groundSpaceES A L)ᗮ.starProjection (e.symm x)) at hh
  exact congrArg e hh

/-- Linear-endomorphism form of canonical local parent commutation with an
arbitrary-boundary MPO. Source: GLM23, `eq:compatible` and lines 1276--1320,
with local adjoint closure stated explicitly. -/
theorem IsBoundaryCompatible.parentInteraction_commute_mpoWithBoundary
    (h : IsBoundaryCompatible T A) (hL : 0 < L)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X L)ᴴ = mpoWithBoundary T Y L)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) :
    Commute (MPSTensor.parentInteraction A L)
      (Matrix.toLin' (mpoWithBoundary T X L)) := by
  apply LinearMap.ext
  intro x
  exact h.parentInteraction_mpoWithBoundary_mulVec hL hstar X x

end MPOTensor
