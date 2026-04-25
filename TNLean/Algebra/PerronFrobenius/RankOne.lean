/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rank-one criteria for the MPDO Perron--Frobenius trace matrix

This module isolates the finite-dimensional matrix step used in Appendix C.2,
Lemma C.4 of arXiv:1606.00608.  The bare Perron--Frobenius statement
"primitive plus constant trace powers implies rank one" is false, so the
usable theorem here records the extra diagonalizability supplied by positive
semidefiniteness.

The main corrected theorem is
`Matrix.PosSemidefTracePowersConstantImpliesRankOne`: if a real finite matrix is
positive semidefinite, has trace one, and has constant traces on all positive
powers, then it factors as an outer product.  Primitivity is not needed for this
strengthened statement; it remains in the surrounding MPDO interface because it
is part of the paper's construction of the auxiliary matrix `T`.
-/

open BigOperators
open scoped BigOperators Matrix

namespace Matrix

variable {n : ℕ}

/-- A square real matrix has the rank-one factorization of Appendix C.2,
Lemma C.4 if it is an outer product `a bᵀ`, represented in Lean as
`Matrix.vecMulVec a b`. -/
def HasRankOneFactorization (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ a b : Fin n → ℝ, T = Matrix.vecMulVec a b

/-- The traces of all positive powers of `T` agree with the trace of `T`
itself. This is the matrix-theoretic consequence of the ZCL step used in
Appendix C.2, Lemma C.4. -/
def TracePowersConstant (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → Matrix.trace (T ^ k) = Matrix.trace T

/-- The scoped Perron--Frobenius input for Appendix C.2, Lemma C.4.

This predicate is retained as a compatibility interface for files that still
phrase the rank-one step as a local hypothesis. As a universally quantified
statement over primitive nonnegative real matrices it is false: there exist
primitive nonnegative matrices with constant trace powers and rank greater than
one. See `TNLean/Archive/PerronFrobeniusRankOneCounterexample.lean`.

The corrected theorem in this module is
`Matrix.PosSemidefTracePowersConstantImpliesRankOne`, which discharges this
predicate whenever the concrete matrix `T` is positive semidefinite and has
trace one. -/
def PrimitiveTracePowersConstantImpliesRankOne
    (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.IsPrimitive T → TracePowersConstant T → HasRankOneFactorization T

/-- A finite family of nonnegative real numbers with sum and sum of squares both
one has exactly one nonzero entry, and that entry is one. -/
private lemma exists_eq_one_of_sum_eq_one_sum_sq_eq_one_nonneg
    {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (h_nonneg : ∀ i, 0 ≤ lam i)
    (h_sum : ∑ i, lam i = 1)
    (h_sq : ∑ i, (lam i) ^ 2 = 1) :
    ∃ i, lam i = 1 ∧ ∀ j, j ≠ i → lam j = 0 := by
  classical
  have hle_one : ∀ i, lam i ≤ 1 := by
    intro i
    calc
      lam i ≤ ∑ j, lam j :=
        Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)
      _ = 1 := h_sum
  have hterm_nonneg : ∀ i, 0 ≤ lam i * (1 - lam i) := by
    intro i
    exact mul_nonneg (h_nonneg i) (sub_nonneg.mpr (hle_one i))
  have hsum_term : ∑ i, lam i * (1 - lam i) = 0 := by
    calc
      ∑ i, lam i * (1 - lam i) = ∑ i, (lam i - (lam i) ^ 2) := by
        simp [mul_sub, pow_two]
      _ = (∑ i, lam i) - ∑ i, (lam i) ^ 2 := by
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [h_sum, h_sq]; norm_num
  have hterm_zero : ∀ i, lam i * (1 - lam i) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hterm_nonneg j)).mp hsum_term i (Finset.mem_univ i)
  have hex : ∃ i, lam i = 1 := by
    by_contra hno
    have hall_zero : ∀ i, lam i = 0 := by
      intro i
      have hz := hterm_zero i
      have hcases : lam i = 0 ∨ 1 - lam i = 0 := by
        exact mul_eq_zero.mp hz
      rcases hcases with h0 | h1
      · exact h0
      · exfalso
        apply hno
        exact ⟨i, by linarith⟩
    have hsum0 : ∑ i, lam i = 0 := by simp [hall_zero]
    linarith
  rcases hex with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  have hsum_erase : (Finset.univ.erase i).sum lam = 0 := by
    have hdecomp :=
      Finset.sum_erase_add (s := Finset.univ) (a := i) (f := lam) (Finset.mem_univ i)
    rw [h_sum, hi] at hdecomp
    linarith
  intro j hji
  have hj_mem : j ∈ Finset.univ.erase i := by simp [hji]
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => h_nonneg k)).mp hsum_erase j hj_mem

/-- Diagonal version of the trace-one/square-trace-one rank-one criterion. -/
private lemma diagonal_hasRankOneFactorization
    (d : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ d i)
    (h_sum : ∑ i, d i = 1)
    (h_sq : ∑ i, (d i) ^ 2 = 1) :
    HasRankOneFactorization (Matrix.diagonal d) := by
  classical
  rcases exists_eq_one_of_sum_eq_one_sum_sq_eq_one_nonneg d h_nonneg h_sum h_sq with
    ⟨i, hi, hzero⟩
  refine ⟨Pi.single i 1, Pi.single i 1, ?_⟩
  ext j k
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i
    · subst k
      simp [Matrix.diagonal, Matrix.vecMulVec, hi]
    · have hik : i ≠ k := fun h => hki h.symm
      simp [Matrix.diagonal, Matrix.vecMulVec, hki, hik]
  · have hjzero : d j = 0 := hzero j hji
    by_cases hki : k = i
    · subst k
      simp [Matrix.diagonal, Matrix.vecMulVec, hji]
    · simp [Matrix.diagonal, Matrix.vecMulVec, hji, hki, hjzero]

/-- Rank-one factorizations are preserved by unitary conjugation. -/
private lemma hasRankOneFactorization_unitary_conj
    (U : Matrix.unitaryGroup (Fin n) ℝ) {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : HasRankOneFactorization T) :
    HasRankOneFactorization
      ((U : Matrix (Fin n) (Fin n) ℝ) * T * star (U : Matrix (Fin n) (Fin n) ℝ)) := by
  classical
  rcases hT with ⟨a, b, rfl⟩
  refine ⟨(U : Matrix (Fin n) (Fin n) ℝ) *ᵥ a,
    fun j => ∑ k, b k * (star (U : Matrix (Fin n) (Fin n) ℝ)) k j, ?_⟩
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  ring_nf

/-- For a positive semidefinite real matrix, the trace of the square is the sum
of the squares of its Hermitian eigenvalues. -/
theorem PosSemidef.trace_sq_eq_sum_eigenvalues_sq
    {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.PosSemidef) :
    Matrix.trace (T ^ 2) = ∑ i, (hT.isHermitian.eigenvalues i) ^ 2 := by
  let hH : T.IsHermitian := hT.isHermitian
  let U := hH.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℝ := diagonal hH.eigenvalues
  have hspec : T = (Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U) D := by
    simpa [D, U] using hH.spectral_theorem
  calc
    Matrix.trace (T ^ 2) =
        Matrix.trace (((Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U) D) ^ 2) := by
      rw [hspec]
    _ = Matrix.trace ((Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U) (D ^ 2)) := by
      rw [map_pow]
    _ = Matrix.trace (D ^ 2) := by
      simp [Unitary.conjStarAlgAut_apply, D, Matrix.trace_mul_cycle]
    _ = ∑ i, (hH.eigenvalues i) ^ 2 := by
      simp [D, diagonal_mul_diagonal, pow_two]

/-- **Corrected rank-one criterion for Lemma C.4.**

If a real finite matrix is positive semidefinite, has trace one, and has
constant trace on all positive powers, then it has a rank-one factorization.
This is the diagonalizable/PSD strengthening missing from the false bare
primitive Perron--Frobenius statement. -/
theorem PosSemidefTracePowersConstantImpliesRankOne
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPSD : T.PosSemidef)
    (hTrace : Matrix.trace T = 1)
    (hTPC : TracePowersConstant T) :
    HasRankOneFactorization T := by
  classical
  let hH : T.IsHermitian := hPSD.isHermitian
  let lam : Fin n → ℝ := hH.eigenvalues
  have hsum : ∑ i, lam i = 1 := by
    have htrace := hH.trace_eq_sum_eigenvalues
    change Matrix.trace T = ∑ i, (lam i : ℝ) at htrace
    rw [hTrace] at htrace
    exact htrace.symm
  have htrace2 : Matrix.trace (T ^ 2) = 1 := by
    calc
      Matrix.trace (T ^ 2) = Matrix.trace T := hTPC 2 (by norm_num)
      _ = 1 := hTrace
  have hsq : ∑ i, (lam i) ^ 2 = 1 := by
    have htrace2eig := hPSD.trace_sq_eq_sum_eigenvalues_sq
    change Matrix.trace (T ^ 2) = ∑ i, (lam i) ^ 2 at htrace2eig
    rw [htrace2] at htrace2eig
    exact htrace2eig.symm
  have hnonneg : ∀ i, 0 ≤ lam i := by
    intro i
    exact hPSD.eigenvalues_nonneg i
  have hD : HasRankOneFactorization (Matrix.diagonal lam) :=
    diagonal_hasRankOneFactorization lam hnonneg hsum hsq
  let U := hH.eigenvectorUnitary
  have hconj : HasRankOneFactorization
      ((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal lam *
        star (U : Matrix (Fin n) (Fin n) ℝ)) :=
    hasRankOneFactorization_unitary_conj U hD
  have hspec :
      T = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal lam *
        star (U : Matrix (Fin n) (Fin n) ℝ) := by
    change T = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal hH.eigenvalues *
      star (U : Matrix (Fin n) (Fin n) ℝ)
    simpa [Unitary.conjStarAlgAut_apply] using hH.spectral_theorem
  rcases hconj with ⟨a, b, hab⟩
  exact ⟨a, b, by rw [hspec, hab]⟩

/-- Positive semidefiniteness and trace normalization discharge the scoped
primitive rank-one predicate. The primitive hypothesis is accepted and ignored:
the PSD theorem is stronger once the trace normalization is available. -/
theorem primitiveTracePowersConstantImpliesRankOne_of_posSemidef
    {T : Matrix (Fin n) (Fin n) ℝ}
    (hPSD : T.PosSemidef) (hTrace : Matrix.trace T = 1) :
    PrimitiveTracePowersConstantImpliesRankOne T := by
  intro _hPrimitive hTPC
  exact PosSemidefTracePowersConstantImpliesRankOne T hPSD hTrace hTPC

end Matrix
