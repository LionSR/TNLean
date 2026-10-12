/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Conjugation by an involution

For an involution \(Q\) and an operation \(\mathrm{op}\) on square matrices
with \(\mathrm{op}(QX)=\mathrm{op}(X)Q\), the equation
\(Q\mathrm{op}(X)Q=X\) is equivalent to \(\mathrm{op}(QX)=QX\).

## Main result

* `Matrix.swapCombined_fixed_iff_leftMul`: the equivalence above.

Source: arXiv:1703.09188, Section `othersymmetries`, lines 1295--1322.
-/

namespace Matrix

/-- For an involution \(Q\), an operation satisfying
\(\mathrm{op}(QX)=\mathrm{op}(X)Q\) converts the equation
\(Q\mathrm{op}(X)Q=X\) into \(\mathrm{op}(QX)=QX\).
This is the matrix argument in arXiv:1703.09188, Section `othersymmetries`,
lines 1295--1322, and Lemma `lemma:sym-trafo-swap`. -/
theorem swapCombined_fixed_iff_leftMul {n : Type*} [Fintype n] [DecidableEq n]
    (Q X : Matrix n n ℂ) (hQ : Q * Q = 1)
    (op : Matrix n n ℂ → Matrix n n ℂ) (hop : op (Q * X) = op X * Q) :
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
