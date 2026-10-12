/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Basic

/-!
# Fixed equations conjugated by an involution

For an involution \(Q\) of a square matrix space and an operation
\(\mathrm{op}\) satisfying \(\mathrm{op}(QX)=\mathrm{op}(X)Q\), the equation
\(Q\,\mathrm{op}(X)\,Q=X\) is equivalent to \(\mathrm{op}(QX)=QX\). This
is the matrix argument that converts swap-combined symmetry equations of
matrix product unitaries into ordinary ones.

Source: arXiv:1703.09188, Section `othersymmetries`, lines 1295--1322, and
Lemma `lemma:sym-trafo-swap`.
-/

namespace Matrix

/-- For an involution \(Q\), an operation satisfying
\(\mathrm{op}(QX)=\mathrm{op}(X)Q\) converts the equation
\(Q\mathrm{op}(X)Q=X\) into \(\mathrm{op}(QX)=QX\).
This is the matrix argument in arXiv:1703.09188, Section `othersymmetries`,
lines 1295--1322, and Lemma `lemma:sym-trafo-swap`. -/
theorem involution_conj_eq_iff_leftMul {n R : Type*} [Fintype n] [DecidableEq n]
    [Semiring R] (Q X : Matrix n n R) (hQ : Q * Q = 1)
    (op : Matrix n n R → Matrix n n R) (hop : op (Q * X) = op X * Q) :
    Q * op X * Q = X ↔ op (Q * X) = Q * X := by
  rw [hop]
  constructor
  · intro h
    simpa only [← Matrix.mul_assoc, hQ, Matrix.one_mul] using
      congrArg (fun Y ↦ Q * Y) h
  · intro h
    calc
      Q * op X * Q = Q * (op X * Q) := Matrix.mul_assoc ..
      _ = Q * (Q * X) := congrArg (fun Y ↦ Q * Y) h
      _ = X := by rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]

end Matrix
