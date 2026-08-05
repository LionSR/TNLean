/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PerronFrobenius.Idempotent
import TNLean.Algebra.PerronFrobenius.Substochastic

/-!
# Perron eigenvector for a primitive matrix with `T² = T³`

This file constructs a strictly positive eigenvector, with eigenvalue exactly `1`, for a
primitive real matrix `T` satisfying `T² = T³`, and the induced diagonal conjugation of
`T` into a row-stochastic primitive matrix. This is the ingredient needed by the Lemma C.5
Case-I singleton-sector route (see issue tracker `#5548`, prerequisite for `#5436`):
the paper's own citation-based step from primitivity and constant positive-power traces to
a rank-one factorization is not valid in general (a counterexample is recorded in
`TNLean/Archive/PerronFrobeniusRankOneCounterexample.lean` and
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`); this file supplies the correct Perron-vector
ingredient consumed by `trace_pow_similarity_diagonal`
(`TNLean/MPS/MPDO/LemmaC5CaseI.lean`) for the corrected, source-faithful replacement
argument (issue `#5404`'s "source-faithful route").

The construction is elementary: `T² = T³` and primitivity already give (via
`IsPrimitive.exists_pos_pow_two_eq_vecMulVec_of_pow_two_eq_pow_three`) a positive rank-one
factorization `T² = a bᵀ` with `a ⬝ᵥ b = 1`. Since `T² a = a`, the vector `v = a + T a` is a
strictly positive eigenvector of `T` itself with eigenvalue `1`: `T v = T a + T² a = T a + a
= v`. No general Perron-Frobenius existence theorem (e.g. via Brouwer's fixed-point theorem
on the probability simplex) is needed for this specialized case.

## Main declarations

* `Matrix.IsPrimitive.exists_pos_eigenvector_one_of_pow_two_eq_pow_three`: existence of the
  positive eigenvalue-`1` eigenvector.
* `Matrix.IsPrimitive.exists_rowStochastic_diagonal_conj_of_pow_two_eq_pow_three`: the
  diagonal conjugate of `T` by this eigenvector is row-stochastic and primitive.
-/

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A primitive matrix `T` with `T² = T³` has a strictly positive eigenvector with
eigenvalue exactly `1`.

The vector is `v = a + T a`, where `T² = vecMulVec a b` is the positive rank-one
factorization of `T²` given by
`IsPrimitive.exists_pos_pow_two_eq_vecMulVec_of_pow_two_eq_pow_three`. -/
theorem IsPrimitive.exists_pos_eigenvector_one_of_pow_two_eq_pow_three
    {T : Matrix n n ℝ} (hT : T.IsPrimitive) (hTsq : T ^ 2 = T ^ 3) :
    ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ T.mulVec v = v := by
  obtain ⟨a, b, ha, hb, hT2, hab⟩ :=
    hT.exists_pos_pow_two_eq_vecMulVec_of_pow_two_eq_pow_three hTsq
  have hT2a : (T ^ 2).mulVec a = a := by
    rw [hT2]
    ext i
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct]
    have hfactor : (∑ x, a i * b x * a x) = a i * ∑ x, b x * a x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hfactor, show (∑ x, b x * a x) = b ⬝ᵥ a from rfl, dotProduct_comm b a, hab, mul_one]
  set u : n → ℝ := T.mulVec a with hu
  have hu_pos : ∀ i, 0 < u i := by
    intro i
    have hrow_nonzero : ∃ j, 0 < T i j := by
      by_contra hcon
      push Not at hcon
      have hrow_zero : ∀ j, T i j = 0 := fun j => le_antisymm (hcon j) (hT.nonneg i j)
      have : (T * T) i i = 0 := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro j _
        rw [hrow_zero j, zero_mul]
      have hT2ii : (T ^ 2) i i = 0 := by rw [sq]; exact this
      rw [hT2] at hT2ii
      simp only [Matrix.vecMulVec_apply] at hT2ii
      have : a i * b i = 0 := hT2ii
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ha i).ne'
      · exact absurd h (hb i).ne'
    obtain ⟨j, hj⟩ := hrow_nonzero
    calc (0 : ℝ) < T i j * a j := mul_pos hj (ha j)
      _ ≤ u i := by
        rw [hu]
        change T i j * a j ≤ ∑ k, T i k * a k
        exact Finset.single_le_sum (f := fun k => T i k * a k)
          (fun k _ => mul_nonneg (hT.nonneg i k) (ha k).le) (Finset.mem_univ j)
  have hTu : T.mulVec u = a := by
    rw [hu, Matrix.mulVec_mulVec, ← sq, hT2a]
  refine ⟨a + u, fun i => add_pos (ha i) (hu_pos i), ?_⟩
  rw [Matrix.mulVec_add, hTu, ← hu]
  ext i
  simp only [Pi.add_apply]
  ring

/-- For a primitive matrix `T` with `T² = T³`, conjugating by the diagonal of the positive
eigenvalue-`1` eigenvector `v` gives a row-stochastic, primitive matrix `D⁻¹ T D`. -/
theorem IsPrimitive.exists_rowStochastic_diagonal_conj_of_pow_two_eq_pow_three
    {T : Matrix n n ℝ} (hT : T.IsPrimitive) (hTsq : T ^ 2 = T ^ 3) :
    ∃ v : n → ℝ, (∀ i, 0 < v i) ∧
      ((Matrix.diagonal v)⁻¹ * T * Matrix.diagonal v) ∈ Matrix.rowStochastic ℝ n ∧
      ((Matrix.diagonal v)⁻¹ * T * Matrix.diagonal v).IsPrimitive := by
  obtain ⟨v, hv, hTv⟩ := hT.exists_pos_eigenvector_one_of_pow_two_eq_pow_three hTsq
  have hdet : IsUnit ((Matrix.diagonal v).det) := by
    rw [Matrix.det_diagonal]
    exact IsUnit.prod_univ_iff.mpr fun i => (hv i).ne'.isUnit
  have hinv : (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun i => (v i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    simp [Matrix.diagonal_mul_diagonal, fun i => (hv i).ne']
  have hPapply : ∀ i j, ((Matrix.diagonal v)⁻¹ * T * Matrix.diagonal v) i j =
      (v i)⁻¹ * T i j * v j := by
    intro i j
    rw [hinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hPnn : ∀ i j, 0 ≤ ((Matrix.diagonal v)⁻¹ * T * Matrix.diagonal v) i j := by
    intro i j
    rw [hPapply]
    exact mul_nonneg (mul_nonneg (inv_pos.mpr (hv i)).le (hT.nonneg i j)) (hv j).le
  refine ⟨v, hv, ?_, ?_⟩
  · rw [Matrix.mem_rowStochastic]
    refine ⟨hPnn, ?_⟩
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, hPapply]
    have hfactor : (∑ j, (v i)⁻¹ * T i j * v j) = (v i)⁻¹ * ∑ j, T i j * v j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hfactor, show (∑ j, T i j * v j) = T.mulVec v i from rfl, hTv,
      inv_mul_cancel₀ (hv i).ne']
  · have hPpow : ∀ k, ((Matrix.diagonal v)⁻¹ * T * Matrix.diagonal v) ^ k =
        (Matrix.diagonal v)⁻¹ * T ^ k * Matrix.diagonal v := by
      intro k
      induction k with
      | zero => simp [Matrix.nonsing_inv_mul _ hdet]
      | succ k ih =>
        rw [pow_succ, pow_succ, ih]
        calc
          (Matrix.diagonal v)⁻¹ * T ^ k * Matrix.diagonal v *
              ((Matrix.diagonal v)⁻¹ * T * Matrix.diagonal v) =
            (Matrix.diagonal v)⁻¹ * T ^ k *
              (Matrix.diagonal v * (Matrix.diagonal v)⁻¹) * T * Matrix.diagonal v := by
            simp [Matrix.mul_assoc]
          _ = (Matrix.diagonal v)⁻¹ * T ^ k * 1 * T * Matrix.diagonal v := by
            rw [Matrix.mul_nonsing_inv _ hdet]
          _ = (Matrix.diagonal v)⁻¹ * T ^ (k + 1) * Matrix.diagonal v := by
            simp [pow_succ, Matrix.mul_assoc]
    obtain ⟨k, hk_pos, hk⟩ := hT.exists_pos_pow
    refine ⟨fun i j => hPnn i j, k, hk_pos, fun i j => ?_⟩
    rw [hPpow, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact mul_pos (mul_pos (inv_pos.mpr (hv i)) (hk i j)) (hv j)

end Matrix
