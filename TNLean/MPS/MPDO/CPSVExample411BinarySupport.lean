/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixCyclicTracePower
import TNLean.MPS.MPDO.CyclicEdgeWeightTensor

/-!
# Effective binary-support model for CPSV16 Example 4.11

This module formalizes the classical binary cycle carried by the support of the
four diagonal neighboring operators printed in CPSV16 Example 4.11. Its
coefficient matrix, extracted from those operators, is
\[
  W=\begin{pmatrix}1&1/2\\1/2&1\end{pmatrix}.
\]
The resulting cyclic-edge tensor has an exact diagonal MPO formula, and its
partition function is
\[
  Z_N=\operatorname{tr}(W^N)=\frac{3^N+1}{2^N}
\]
for every positive length.

**Scope restriction (supported binary encoding):** the physical dimension in
this module is $2$. A supported label $k$ selects the ambient two-qubit basis
vector $|k,k\rangle$ at each site. The literal tensor printed in the paper has
physical dimension $4$; identifying it requires a later support embedding. See
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. No spectrum, entropy,
SAL, ZCL, or ambient-tensor equivalence is asserted here.

## Main definitions

* `weightMatrix`: the coefficient matrix extracted from the four printed diagonal
  neighboring operators.
* `edgeWeight`: the diagonal ket--bra edge weight.
* `M`: the associated cyclic-edge matrix-product tensor.
* `cycleWeight`: the unnormalized weight of a binary cycle labeling.
* `partitionFunction`: the sum of all binary cycle weights.

## Main results

* `mpo_M_apply`: the exact positive-length diagonal MPO entry formula.
* `mpo_M_eq_diagonal`: the corresponding matrix formula.
* `partitionFunction_eq_trace_pow`: the cycle sum equals `tr(W^N)`.
* `trace_weightMatrix_pow`: the closed trace-power formula.
* `partitionFunction_closed_form`: the closed positive-length normalization.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor.CPSVExample411BinarySupport

/-- The coefficient matrix extracted from the four diagonal neighboring
operators printed in CPSV16 Example 4.11.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def weightMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1 / 2; 1 / 2, 1]

/-- The scalar edge weight, diagonal in both endpoint ket--bra pairs.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def edgeWeight (i j i' j' : Fin 2) : ℂ :=
  if i = j ∧ i' = j' then weightMatrix i i' else 0

/-- The bond-dimension-$4$ cyclic-edge tensor for the effective binary model.
A supported physical label $k$ selects the ambient basis vector $|k,k\rangle$.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def M : MPOTensor 2 4 := cyclicEdgeWeightTensor edgeWeight

/-- The unnormalized weight of a binary labeling of a periodic cycle.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def cycleWeight {N : ℕ} [NeZero N] (σ : Fin N → Fin 2) : ℂ :=
  ∏ n : Fin N, weightMatrix (σ n) (σ (n + 1))

/-- The partition function obtained by summing all binary cycle weights.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def partitionFunction (N : ℕ) [NeZero N] : ℂ :=
  ∑ σ : Fin N → Fin 2, cycleWeight σ

/-- The effective binary tensor has exactly the expected diagonal cycle entries.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
theorem mpo_M_apply {N : ℕ} [NeZero N] (σ τ : Fin N → Fin 2) :
    mpo M N σ τ = if σ = τ then cycleWeight σ else 0 := by
  rw [M, mpo_cyclicEdgeWeightTensor]
  by_cases hστ : σ = τ
  · subst τ
    simp only [edgeWeight, cycleWeight, true_and, ↓reduceIte]
  · rw [if_neg hστ]
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hστ
    apply Finset.prod_eq_zero (Finset.mem_univ n)
    simp only [edgeWeight]
    rw [if_neg]
    exact fun hdiag ↦ hn hdiag.1

/-- The diagonal MPO matrix formula, as an equality of matrices.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
theorem mpo_M_eq_diagonal {N : ℕ} [NeZero N] :
    mpo M N = Matrix.diagonal cycleWeight := by
  ext σ τ
  rw [mpo_M_apply, Matrix.diagonal_apply]

/-- The binary cycle partition function is the trace of the corresponding
matrix power.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
theorem partitionFunction_eq_trace_pow {N : ℕ} [NeZero N] :
    partitionFunction N = Matrix.trace (weightMatrix ^ N) := by
  rw [partitionFunction, trace_pow_eq_sum_cyclic_product]
  simp only [cycleWeight]

private def hadamard : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

private def eigenvalueMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![3 / 2, 1 / 2]

private lemma hadamard_mul_half_hadamard :
    hadamard * ((1 / 2 : ℂ) • hadamard) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

private lemma half_hadamard_mul_hadamard :
    ((1 / 2 : ℂ) • hadamard) * hadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

private lemma hadamard_mul_eigenvalueMatrix_eq_weightMatrix_mul_hadamard :
    hadamard * eigenvalueMatrix = weightMatrix * hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, eigenvalueMatrix, weightMatrix, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num

private lemma hadamard_mul_eigenvalueMatrix_pow_eq_weightMatrix_pow_mul_hadamard
    (N : ℕ) :
    hadamard * eigenvalueMatrix ^ N = weightMatrix ^ N * hadamard := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        hadamard_mul_eigenvalueMatrix_eq_weightMatrix_mul_hadamard,
        ← Matrix.mul_assoc]

private lemma trace_weightMatrix_pow_eq_trace_eigenvalueMatrix_pow (N : ℕ) :
    Matrix.trace (weightMatrix ^ N) = Matrix.trace (eigenvalueMatrix ^ N) := by
  have h := hadamard_mul_eigenvalueMatrix_pow_eq_weightMatrix_pow_mul_hadamard N
  have hdiag : eigenvalueMatrix ^ N =
      ((1 / 2 : ℂ) • hadamard) * weightMatrix ^ N * hadamard := by
    have h' : ((1 / 2 : ℂ) • hadamard) * (hadamard * eigenvalueMatrix ^ N) =
        ((1 / 2 : ℂ) • hadamard) * (weightMatrix ^ N * hadamard) := by
      rw [h]
    simp only [← Matrix.mul_assoc] at h'
    rwa [half_hadamard_mul_hadamard, one_mul] at h'
  rw [hdiag, Matrix.trace_mul_cycle, hadamard_mul_half_hadamard, one_mul]

/-- The trace of every power of the coefficient matrix extracted from the four
printed diagonal neighboring operators has the closed form
`(3^N + 1) / 2^N`.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
theorem trace_weightMatrix_pow (N : ℕ) :
    Matrix.trace (weightMatrix ^ N) = ((3 : ℂ) ^ N + 1) / (2 : ℂ) ^ N := by
  rw [trace_weightMatrix_pow_eq_trace_eigenvalueMatrix_pow,
    eigenvalueMatrix, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [Fin.sum_univ_two, Pi.pow_apply, Matrix.vecEmpty, Matrix.vecCons]
  change ((3 : ℂ) / 2) ^ N + ((1 : ℂ) / 2) ^ N =
    ((3 : ℂ) ^ N + 1) / (2 : ℂ) ^ N
  rw [div_pow, div_pow]
  field_simp
  ring

/-- The exact positive-length normalization of the effective binary model.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
theorem partitionFunction_closed_form {N : ℕ} [NeZero N] :
    partitionFunction N = ((3 : ℂ) ^ N + 1) / (2 : ℂ) ^ N := by
  rw [partitionFunction_eq_trace_pow, trace_weightMatrix_pow]

end MPOTensor.CPSVExample411BinarySupport
