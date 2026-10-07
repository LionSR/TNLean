/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Exact factorizations of idempotent matrices

An idempotent matrix admits a factorization `P = W * V` with `V * W = 1`,
where the inner dimension is exactly the rank of `P`. The idempotent need not
be Hermitian. The construction chooses coordinates on its range and uses `P`
itself to define the coordinate projection.

This is the elementary range-splitting step in the finite-dimensional
representation argument of Garre-Rubio, Lootens and Molnár, arXiv:2203.12563v3,
Appendix A. It also applies to non-unital representations, whose support is
an idempotent rather than the ambient identity.
-/

open scoped Matrix

namespace Matrix

/-- An idempotent factors through its range with a left inverse. No adjoint or
self-adjointness assumption is needed, and rank zero is allowed. -/
theorem exists_rankFactorization_of_idempotent
    {K : Type*} [Field K] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (hP : P * P = P) :
    ∃ (W : Matrix (Fin n) (Fin P.rank) K) (V : Matrix (Fin P.rank) (Fin n) K),
      V * W = 1 ∧ W * V = P := by
  classical
  let f := P.mulVecLin
  let e : (Fin P.rank → K) ≃ₗ[K] LinearMap.range f :=
    (Module.finBasisOfFinrankEq K (LinearMap.range f) rfl).equivFun.symm
  let W := LinearMap.toMatrix' ((LinearMap.range f).subtype.comp e.toLinearMap)
  let V := LinearMap.toMatrix' (e.symm.toLinearMap.comp f.rangeRestrict)
  have hW (x : Fin P.rank → K) : W *ᵥ x = (e x : Fin n → K) := by
    simp [W]
  have hV (x : Fin n → K) : e (V *ᵥ x) = f.rangeRestrict x := by
    simp [V]
  have hfix (x : LinearMap.range f) : f (x : Fin n → K) = x := by
    obtain ⟨y, hy⟩ := x.property
    change P *ᵥ (x : Fin n → K) = x
    rw [← hy]
    change P *ᵥ (P *ᵥ y) = P *ᵥ y
    rw [mulVec_mulVec, hP]
  refine ⟨W, V, ?_, ?_⟩
  · apply Matrix.ext_iff_mulVec.2
    intro x
    rw [← mulVec_mulVec, one_mulVec, hW]
    apply e.injective
    rw [hV]
    apply Subtype.ext
    exact hfix (e x)
  · apply Matrix.ext_iff_mulVec.2
    intro x
    rw [← mulVec_mulVec, hW, hV]
    rfl

end Matrix
