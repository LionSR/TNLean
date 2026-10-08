/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # Mixed density matrices of finite weighted operator sums -/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-corrections-matrixdensitysum-01
Downstream declaration:
Matrix.sum_smul_mul_mul_conjTranspose

-/

open scoped Matrix ComplexConjugate

namespace Matrix

/-- A finite sum on each side of a rectangular input matrix gives the mixed
ket–bra sum with the bra coefficients conjugated. -/
theorem sum_smul_mul_mul_conjTranspose {α β m n p q : Type*}
    [Fintype α] [Fintype β] [Fintype n] [Fintype q]
    (c : α → ℂ) (d : β → ℂ) (K : α → Matrix m n ℂ)
    (L : β → Matrix p q ℂ) (ρ : Matrix n q ℂ) :
    (∑ a, c a • K a) * ρ * (∑ b, d b • L b)ᴴ =
      ∑ a, ∑ b, (c a * conj (d b)) • (K a * ρ * (L b)ᴴ) := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul, Complex.star_def]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end Matrix
