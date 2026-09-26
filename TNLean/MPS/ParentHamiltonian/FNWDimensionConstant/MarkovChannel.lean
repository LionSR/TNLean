/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWDimensionConstant.MarkovMatrix
import TNLean.MPS.ParentHamiltonian.FNWDimensionConstant.MatrixUnitNormalization

/-!
# The channel of the positive Markov matrix-unit tensor

For the original construction used to examine Nachtergaele, Section 6, equation
`boundAm` (arXiv:cond-mat/9410110, lines 2401--2412), the physical letters are
\(A_{ij}=\sqrt{P_{ij}}E_{ij}\). Strict positivity makes this tensor injective,
and double stochasticity makes its transfer map both unital and trace preserving.
Its third power is the completely depolarizing channel.
-/

open scoped BigOperators Matrix

namespace MPSTensor.FNWDimensionConstant

/-- The weighted matrix-unit tensor associated with the positive Markov matrix. -/
noncomputable def markovTensor : MPSTensor 16 4 := matrixUnitTensor markovAmplitude

/-- The transfer map of a weighted matrix-unit tensor acts only on diagonal entries. -/
theorem transferMap_matrixUnitTensor {k : ℕ} (t : Matrix (Fin k) (Fin k) ℝ)
    (X : Matrix (Fin k) (Fin k) ℂ) :
    Kraus.transferMap (matrixUnitTensor t) X =
      Matrix.diagonal (fun i ↦ ∑ j, (t i j : ℂ) ^ 2 * X j j) := by
  rw [Kraus.transferMap_apply, ← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, matrixUnitTensor_apply, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single]
  ext i j
  simp [Matrix.sum_apply, Matrix.single, Matrix.diagonal, ite_and, pow_two, mul_comm,
    mul_left_comm]

private noncomputable def complexMarkovMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  (Rat.castHom ℂ).mapMatrix markovMatrix

private noncomputable def complexUniformMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  (Rat.castHom ℂ).mapMatrix uniformMatrix

private theorem complexMarkovMatrix_pow_three :
    complexMarkovMatrix ^ 3 = complexUniformMatrix := by
  change ((Rat.castHom ℂ).mapMatrix markovMatrix) ^ 3 =
    (Rat.castHom ℂ).mapMatrix uniformMatrix
  rw [← map_pow, markovMatrix_pow_three]

private theorem markovAmplitude_complex_sq (i j : Fin 4) :
    (markovAmplitude i j : ℂ) ^ 2 = (realMarkovMatrix i j : ℂ) := by
  exact_mod_cast markovAmplitude_sq i j

private theorem markovTensor_transferMap_eq_diagonal (X : Matrix (Fin 4) (Fin 4) ℂ) :
    Kraus.transferMap markovTensor X = Matrix.diagonal (complexMarkovMatrix *ᵥ X.diag) := by
  refine (transferMap_matrixUnitTensor markovAmplitude X).trans ?_
  simp [Matrix.mulVec, dotProduct, markovAmplitude_complex_sq,
    complexMarkovMatrix, realMarkovMatrix]

/-- Three transfer steps erase all information except the trace. This exact identity
underlies the prescribed-rate test of Nachtergaele, Section 6, equation `boundAm`. -/
theorem markovTensor_transferMap_cube (X : Matrix (Fin 4) (Fin 4) ℂ) :
    Kraus.transferMap markovTensor (Kraus.transferMap markovTensor
      (Kraus.transferMap markovTensor X)) =
      (Matrix.trace X / 4) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [markovTensor_transferMap_eq_diagonal, Matrix.diag_diagonal,
    Matrix.mulVec_mulVec]
  rw [← pow_two, ← pow_succ', complexMarkovMatrix_pow_three]
  ext i j
  simp [complexUniformMatrix, uniformMatrix, Matrix.mulVec, dotProduct, Matrix.trace,
    Matrix.diag, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
    Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- All matrix units occur with nonzero coefficients, so the tensor is injective. -/
theorem markovTensor_isInjective : Kraus.IsInjective markovTensor :=
  matrixUnitTensor_isInjective markovAmplitude (fun i j ↦ (markovAmplitude_pos i j).ne')

/-- Column stochasticity makes the tensor trace preserving. -/
theorem markovTensor_isTP : Kraus.IsTP markovTensor :=
  matrixUnitTensor_isTP markovAmplitude (fun j ↦ by
    simpa only [markovAmplitude_sq] using realMarkovMatrix_sum_col j)

/-- Row stochasticity makes the transfer map unital. -/
theorem markovTensor_transferMap_one :
    Kraus.transferMap markovTensor (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  refine (transferMap_matrixUnitTensor markovAmplitude 1).trans ?_
  simp [markovAmplitude_complex_sq, ← Complex.ofReal_sum, realMarkovMatrix_sum_row]

end MPSTensor.FNWDimensionConstant
