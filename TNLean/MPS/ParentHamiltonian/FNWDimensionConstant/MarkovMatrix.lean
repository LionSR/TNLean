/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.BigOperators

/-!
# A positive Markov matrix with a nonzero nilpotent remainder

This module records exact rational identities for an original four-dimensional
construction used to examine the prescribed-rate constant in Nachtergaele,
arXiv:cond-mat/9410110, Section 6, equation `boundAm` (local source lines 2401--2412).
The matrix is \(P=J/4+(uv^{\mathsf T}+vw^{\mathsf T})/16\), where \(u,v,w\)
are the three nonconstant Hadamard vectors. It is strictly positive and doubly
stochastic, and satisfies \(P^2=J/4+uw^{\mathsf T}/64\) and \(P^3=J/4\).

These matrix identities alone do not assert a counterexample to the source's
physical ground-space projection estimate. That requires a separate construction
of the tensor and its physical projections.
-/

namespace MPSTensor.FNWDimensionConstant

/-- The first nonconstant Hadamard vector in the original Markov-matrix construction
for the audit of Nachtergaele, Section 6, equation `boundAm`. -/
def hadamardU : Fin 4 → ℚ := ![1, 1, -1, -1]

/-- The second nonconstant Hadamard vector in the original construction for the audit
of Nachtergaele, Section 6, equation `boundAm`. -/
def hadamardV : Fin 4 → ℚ := ![1, -1, 1, -1]

/-- The third nonconstant Hadamard vector in the original construction for the audit
of Nachtergaele, Section 6, equation `boundAm`. -/
def hadamardW : Fin 4 → ℚ := ![1, -1, -1, 1]

/-- The uniform transition matrix \(J/4\). -/
def uniformMatrix : Matrix (Fin 4) (Fin 4) ℚ := fun _ _ ↦ 1 / 4

/-- The positive transition matrix \(J/4+(uv^{\mathsf T}+vw^{\mathsf T})/16\).
This is an original example for the audit of Nachtergaele, Section 6, equation
`boundAm`, rather than a matrix specified in that source. -/
def markovMatrix : Matrix (Fin 4) (Fin 4) ℚ := fun i j ↦
  1 / 4 + (hadamardU i * hadamardV j + hadamardV i * hadamardW j) / 16

/-- The two-step transition matrix with its surviving rank-one term. -/
def squareMatrix : Matrix (Fin 4) (Fin 4) ℚ := fun i j ↦
  1 / 4 + hadamardU i * hadamardW j / 64

/-- The nonconstant part survives for two steps as a rank-one matrix. -/
theorem markovMatrix_pow_two :
    markovMatrix ^ 2 = squareMatrix := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, markovMatrix, squareMatrix,
      hadamardU, hadamardV, hadamardW]

/-- The transition matrix reaches the uniform matrix after three steps. -/
theorem markovMatrix_pow_three : markovMatrix ^ 3 = uniformMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, markovMatrix, uniformMatrix,
      hadamardU, hadamardV, hadamardW]

/-- Every transition probability is strictly positive. -/
theorem markovMatrix_pos : ∀ i j, 0 < markovMatrix i j := by
  norm_num [Fin.forall_fin_succ, markovMatrix, hadamardU, hadamardV, hadamardW]

/-- Row and column sums and the two Hadamard directions annihilated by the matrix. -/
theorem markovMatrix_sum_identities :
    (∀ i, ∑ j, markovMatrix i j = 1) ∧
    (∀ j, ∑ i, markovMatrix i j = 1) ∧
    (∀ i, ∑ j, markovMatrix i j * hadamardU j = 0) ∧
    (∀ j, ∑ i, hadamardW i * markovMatrix i j = 0) ∧
    (∀ i, hadamardU i ^ 2 = 1) ∧ (∀ i, hadamardW i ^ 2 = 1) := by
  norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ, markovMatrix,
    hadamardU, hadamardV, hadamardW]

/-- The same transition probabilities, regarded as real numbers. -/
def realMarkovMatrix : Matrix (Fin 4) (Fin 4) ℝ := fun i j ↦ markovMatrix i j

/-- The real first Hadamard direction. -/
def realHadamardU : Fin 4 → ℝ := fun i ↦ hadamardU i

/-- The real third Hadamard direction. -/
def realHadamardW : Fin 4 → ℝ := fun i ↦ hadamardW i

/-- The real transition probabilities are positive. -/
theorem realMarkovMatrix_pos (i j : Fin 4) : 0 < realMarkovMatrix i j := by
  simp only [realMarkovMatrix]
  exact_mod_cast markovMatrix_pos i j

/-- Each row sums to one. -/
theorem realMarkovMatrix_sum_row (i : Fin 4) : ∑ j, realMarkovMatrix i j = 1 := by
  simp only [realMarkovMatrix]
  exact_mod_cast markovMatrix_sum_identities.1 i

/-- Each column sums to one. -/
theorem realMarkovMatrix_sum_col (j : Fin 4) : ∑ i, realMarkovMatrix i j = 1 := by
  simp only [realMarkovMatrix]
  exact_mod_cast markovMatrix_sum_identities.2.1 j

/-- The matrix annihilates the first Hadamard direction on the right. -/
theorem realMarkovMatrix_mul_hadamardU (i : Fin 4) :
    ∑ j, realMarkovMatrix i j * realHadamardU j = 0 := by
  simp only [realMarkovMatrix, realHadamardU]
  exact_mod_cast markovMatrix_sum_identities.2.2.1 i

/-- The third Hadamard direction annihilates the matrix on the left. -/
theorem realHadamardW_mul_markovMatrix (j : Fin 4) :
    ∑ i, realHadamardW i * realMarkovMatrix i j = 0 := by
  simp only [realMarkovMatrix, realHadamardW]
  exact_mod_cast markovMatrix_sum_identities.2.2.2.1 j

/-- Each entry of the first Hadamard direction has square one. -/
theorem realHadamardU_sq (i : Fin 4) : realHadamardU i ^ 2 = 1 := by
  simp only [realHadamardU]
  exact_mod_cast markovMatrix_sum_identities.2.2.2.2.1 i

/-- Each entry of the third Hadamard direction has square one. -/
theorem realHadamardW_sq (i : Fin 4) : realHadamardW i ^ 2 = 1 := by
  simp only [realHadamardW]
  exact_mod_cast markovMatrix_sum_identities.2.2.2.2.2 i

/-- The real two-step transition probabilities retain a rank-one remainder. -/
theorem realMarkovMatrix_pow_two (i j : Fin 4) :
    (realMarkovMatrix ^ 2 : Matrix (Fin 4) (Fin 4) ℝ) i j =
      1 / 4 + realHadamardU i * realHadamardW j / 64 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, realMarkovMatrix,
      realHadamardU, realHadamardW, markovMatrix, hadamardU, hadamardV, hadamardW]

/-- The real three-step transition probabilities are uniform. -/
theorem realMarkovMatrix_pow_three (i j : Fin 4) :
    (realMarkovMatrix ^ 3 : Matrix (Fin 4) (Fin 4) ℝ) i j = 1 / 4 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, realMarkovMatrix,
      markovMatrix, hadamardU, hadamardV, hadamardW]

private theorem markovMatrix_path_sums :
    (∀ a f, ∑ b, ∑ c, ∑ e, markovMatrix a b * markovMatrix b c *
      markovMatrix c e * markovMatrix e f = 1 / 4) ∧
    (∀ a f, ∑ b, ∑ c, ∑ e, hadamardU b *
      (markovMatrix a b * markovMatrix b c * markovMatrix c e * markovMatrix e f) = 0) ∧
    (∀ a f, ∑ b, ∑ c, ∑ e, hadamardU b * hadamardW e *
      (markovMatrix a b * markovMatrix b c * markovMatrix c e * markovMatrix e f) = 1 / 64) := by
  decide +kernel

/-- The total weight of four-step paths with prescribed endpoints. -/
theorem realMarkovMatrix_path_sum (a f : Fin 4) :
    ∑ b, ∑ c, ∑ e, realMarkovMatrix a b * realMarkovMatrix b c *
      realMarkovMatrix c e * realMarkovMatrix e f = 1 / 4 := by
  simp only [realMarkovMatrix]
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
    congrArg (fun q : ℚ ↦ (q : ℝ)) (markovMatrix_path_sums.1 a f)

/-- Marking the first internal coordinate by the first Hadamard vector has zero mean. -/
theorem realMarkovMatrix_path_hadamardU_sum (a f : Fin 4) :
    ∑ b, ∑ c, ∑ e, realHadamardU b *
      (realMarkovMatrix a b * realMarkovMatrix b c *
        realMarkovMatrix c e * realMarkovMatrix e f) = 0 := by
  simp only [realMarkovMatrix, realHadamardU]
  exact_mod_cast markovMatrix_path_sums.2.1 a f

/-- The two Hadamard marks have nonzero four-step path correlation. -/
theorem realMarkovMatrix_path_hadamardUW_sum (a f : Fin 4) :
    ∑ b, ∑ c, ∑ e, realHadamardU b * realHadamardW e *
      (realMarkovMatrix a b * realMarkovMatrix b c *
        realMarkovMatrix c e * realMarkovMatrix e f) = 1 / 64 := by
  simp only [realMarkovMatrix, realHadamardU, realHadamardW]
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
    congrArg (fun q : ℚ ↦ (q : ℝ)) (markovMatrix_path_sums.2.2 a f)

/-- The square-root amplitudes for the weighted matrix-unit tensor. -/
noncomputable def markovAmplitude : Matrix (Fin 4) (Fin 4) ℝ := fun i j ↦
  Real.sqrt (realMarkovMatrix i j)

/-- Squaring an amplitude recovers its transition probability. -/
theorem markovAmplitude_sq (i j : Fin 4) : markovAmplitude i j ^ 2 = realMarkovMatrix i j := by
  exact Real.sq_sqrt (realMarkovMatrix_pos i j).le

/-- Every matrix-unit amplitude is strictly positive. -/
theorem markovAmplitude_pos (i j : Fin 4) : 0 < markovAmplitude i j := by
  exact Real.sqrt_pos.2 (realMarkovMatrix_pos i j)

/-- The remainder after removing the uniform stationary projection. -/
def remainderMatrix : Matrix (Fin 4) (Fin 4) ℚ := markovMatrix - uniformMatrix

/-- The nonconstant remainder has nilpotency index exactly three. -/
theorem remainderMatrix_nilpotent : remainderMatrix ^ 3 = 0 ∧ remainderMatrix ^ 2 ≠ 0 := by
  decide +kernel

end MPSTensor.FNWDimensionConstant
