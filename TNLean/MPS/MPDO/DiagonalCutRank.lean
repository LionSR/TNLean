/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank of a diagonal matrix-product-operator cut

For a periodic matrix product operator, split a diagonal physical word into two
consecutive blocks.  The resulting matrix of diagonal coefficients factors
through the space of pairs of virtual indices.  Its ordinary complex rank is
therefore at most the square of the bond dimension.

This is the algebraic part of the classical-diagonal analysis of the estimate
in Proposition 4.5 of arXiv:1606.00608.  Combined with Theorem 4.1 of
arXiv:1704.06507, it gives the stronger classical estimate
$I(X:Y) \leq 2\log D$.  The information-versus-rank theorem is formalized in
`TNLean.Entropy.ClassicalMutualInformation`; the scalar normalization and
real-to-complex rank comparison needed for the MPO corollary are not proved in
this file.

## Main definitions

* `MPOTensor.diagonalCutMatrix`: the matrix whose rows and columns are physical
  words on the two sides of a periodic cut and whose entries are the diagonal
  coefficients of the full MPO.

## Main results

* `MPOTensor.diagonalCutMatrix_rank_le`: the diagonal cut matrix of a periodic
  MPO has rank at most $D^2$.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace Matrix

variable {D : ℕ} {r c : Type*} [Fintype c]

/-- The matrix of trace pairings $(x,y) \mapsto \operatorname{tr}(A_xB_y)$
between two finite families of square matrices. -/
private noncomputable def traceMulMatrix
    (A : r → Matrix (Fin D) (Fin D) ℂ)
    (B : c → Matrix (Fin D) (Fin D) ℂ) : Matrix r c ℂ :=
  fun x y ↦ trace (A x * B y)

/-- A matrix of trace pairings of two families of $D\times D$ matrices has
ordinary complex rank at most $D^2$.

This is the finite-dimensional factorization
$\operatorname{tr}(A_xB_y)=\sum_{a,b}(A_x)_{ab}(B_y)_{ba}$. -/
private theorem rank_traceMulMatrix_le
    (A : r → Matrix (Fin D) (Fin D) ℂ)
    (B : c → Matrix (Fin D) (Fin D) ℂ) :
    (traceMulMatrix A B).rank ≤ D * D := by
  classical
  let X : Matrix r (Fin D × Fin D) ℂ := fun x ab ↦ A x ab.1 ab.2
  let Y : Matrix (Fin D × Fin D) c ℂ := fun ab y ↦ B y ab.2 ab.1
  have hfactor : traceMulMatrix A B = X * Y := by
    ext x y
    simp [traceMulMatrix, X, Y, Matrix.mul_apply, Matrix.trace, Fintype.sum_prod_type]
  rw [hfactor]
  refine (Matrix.rank_mul_le_left X Y).trans ?_
  simpa using Matrix.rank_le_card_width X

end Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- The matrix of diagonal coefficients across a cut of a periodic MPO.  A row
is a word of length $L$, a column is a word of length $R$, and the corresponding
entry is
$\operatorname{tr}(M^{x_0x_0}\cdots M^{x_{L-1}x_{L-1}}
M^{y_0y_0}\cdots M^{y_{R-1}y_{R-1}})$.

This is the joint-probability matrix when the generated operator on $L+R$
sites is diagonal, positive semidefinite, and normalized. -/
noncomputable def diagonalCutMatrix (M : MPOTensor d D) (L R : ℕ) :
    Matrix (Fin L → Fin d) (Fin R → Fin d) ℂ :=
  fun x y ↦ Matrix.trace
    (evalWord M (List.ofFn x ++ List.ofFn y) (List.ofFn x ++ List.ofFn y))

/-- The ordinary complex rank of the diagonal coefficient matrix across a
periodic MPO cut is at most $D^2$.

This is the virtual-pair factorization used in the classical-diagonal analysis
of Proposition 4.5 of arXiv:1606.00608; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalCutMatrix_rank_le (M : MPOTensor d D) (L R : ℕ) :
    (diagonalCutMatrix M L R).rank ≤ D * D := by
  classical
  let A : (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun x ↦ evalWord M (List.ofFn x) (List.ofFn x)
  let B : (Fin R → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun y ↦ evalWord M (List.ofFn y) (List.ofFn y)
  have hfactor : diagonalCutMatrix M L R = Matrix.traceMulMatrix A B := by
    ext x y
    simp [diagonalCutMatrix, Matrix.traceMulMatrix, A, B, evalWord_append]
  rw [hfactor]
  exact Matrix.rank_traceMulMatrix_le A B

end MPOTensor
