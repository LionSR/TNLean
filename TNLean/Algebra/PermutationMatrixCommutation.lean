/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Matrices invariant under a simultaneous index permutation

Simultaneous permutation invariance of the entries is equivalent to commuting
with the corresponding permutation matrix. The identity is used in the finite
coordinate symmetry arguments of SCP10, arXiv:1001.3807, lines 2505–2558.
-/

namespace Matrix
variable {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]

/-- A matrix with permutation-invariant entries commutes with the actual permutation
matrix. This is the finite-coordinate symmetry step in SCP10, lines 2505–2558. -/
theorem commute_permMatrix_of_entry_invariant (A : Matrix ι ι R) (τ : Equiv.Perm ι)
    (h : ∀ a b, A (τ a) (τ b) = A a b) : Commute A (τ.permMatrix R) := by
  change A * τ.permMatrix R = τ.permMatrix R * A
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  ext a b
  exact (h a (τ.symm b)).symm.trans (by simp)
end Matrix
