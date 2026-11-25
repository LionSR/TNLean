/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Evaluation
import QICLean.Algebra.Matrix.MatrixDensitySum
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Density coefficients of the chronological partial expansion

The exact chronological operator identity gives an exact ket–bra expansion in
any finite coordinates of the grouped memories. The coordinates are given by
matrices `E` and `F` whose columns are the input and output coordinate vectors,
for instance the vectors of orthonormal bases; the matrix of an operator `T` in
these coordinates is `Fᴴ * T * E`. Its scalar weights are the original ket
coefficients times the conjugates of the bra coefficients. The identity holds
for arbitrary input matrices and needs no condition on `E` and `F`.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 342–381.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section
open scoped ComplexConjugate Matrix
open Matrix ManyBody

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]

/-- In any input and output coordinates `E` and `F` of the grouped memories, the matrix of the
original operator is the weighted sum of the matrices of the branches of the partial expansion,
every original complex coefficient being kept. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 351–381. -/
theorem matrix_eval_eq_sum_partialWord {m n : Type} (A : P → Bool) (w : SourceCircuit X Y)
    (E : Matrix (Config (blockSystem (affectedOwner A) X)) n ℂ)
    (F : Matrix (Config (blockSystem (affectedOwner A) Y)) m ℂ) :
    Fᴴ * reindex (blockConfigEquiv (affectedOwner A) Y).symm
        (blockConfigEquiv (affectedOwner A) X).symm w.op * E =
      ∑ ξ, coefficient A w ξ • (Fᴴ * Word.op (partialWord A w ξ) * E) := by
  rw [← sum_coefficient_smul_op_partialWord A w, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The density calculation has independent partial choices on its ket and bra
sides, weighted by the original coefficient and the conjugate bra coefficient.
Untouched gates remain aggregate operators in every summand. The matrices are taken in any
input and output coordinates `E` and `F`, for instance orthonormal bases. No positivity or
normalization assumption on the input matrix is required.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–381. -/
theorem density_eval_eq_sum_partialWord {m n : Type} [Fintype n] (A : P → Bool)
    (w : SourceCircuit X Y) (E : Matrix (Config (blockSystem (affectedOwner A) X)) n ℂ)
    (F : Matrix (Config (blockSystem (affectedOwner A) Y)) m ℂ) (ρ : Matrix n n ℂ) :
    let M := Fᴴ * reindex (blockConfigEquiv (affectedOwner A) Y).symm
      (blockConfigEquiv (affectedOwner A) X).symm w.op * E
    let K := fun ξ ↦ Fᴴ * Word.op (partialWord A w ξ) * E
    M * ρ * Mᴴ = ∑ ξ, ∑ ζ,
      (coefficient A w ξ * conj (coefficient A w ζ)) • (K ξ * ρ * (K ζ)ᴴ) := by
  dsimp only
  rw [matrix_eval_eq_sum_partialWord A w E F]
  exact Matrix.sum_smul_mul_mul_conjTranspose _ _ _ _ _

end QuantumCircuit.Party.SourceCircuit
