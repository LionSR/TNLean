/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Summing source errors and choosing the sample count

Errors indexed by nonempty subsets of the original source occurrences sum
to a binomial expression. An explicit integer sample count bounds this
expression by one quarter of the prescribed error. Its upper bound is
quadratic in the number of sources, the coefficient bound, and the inverse
accuracy. The estimates also cover a circuit with no source occurrences.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 540–558.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-total-error.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-sourcesamplingcount-01
Downstream declaration:
TNLean.PEPS.Approximation.div_sqrt_sourceSamplingCount_le

Provenance-ID: 8769-physical-sourcesamplingcount-02
Downstream declaration:
TNLean.PEPS.Approximation.sourceSamplingCount

Provenance-ID: 8769-physical-sourcesamplingcount-03
Downstream declaration:
TNLean.PEPS.Approximation.sourceSamplingCount_lt

Provenance-ID: 8769-physical-sourcesamplingcount-04
Downstream declaration:
TNLean.PEPS.Approximation.sourceSamplingCount_pos

Provenance-ID: 8769-physical-sourcesamplingcount-05
Downstream declaration:
TNLean.PEPS.Approximation.sum_nonemptyFinsets_pow_card

Provenance-ID: 8769-physical-sourcesamplingcount-06
Downstream declaration:
TNLean.PEPS.Approximation.sum_sourceErrorWeights

Provenance-ID: 8769-physical-sourcesamplingcount-07
Downstream declaration:
TNLean.PEPS.Approximation.sum_sourceErrorWeights_sourceSamplingCount_le

-/


noncomputable section
namespace TNLean.PEPS.Approximation

open Classical in
/-- The sum of the cardinality weights over all nonempty subsets. -/
theorem sum_nonemptyFinsets_pow_card {E : Type*} [Fintype E] (q : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset E)).erase ∅, q ^ S.card) =
      (1 + q) ^ Fintype.card E - 1 := by
  have h := Finset.prod_one_add (f := fun _ : E ↦ q) Finset.univ
  simp only [Finset.prod_const, Finset.card_univ, Finset.powerset_univ] at h
  have he := Finset.sum_erase_add (Finset.univ : Finset (Finset E))
    (fun S ↦ q ^ S.card) (Finset.mem_univ ∅)
  simp only [Finset.card_empty, pow_zero] at he
  linarith

open Classical in
/-- The Gaussian inverse-sample factor converts the subset sum to the
binomial expression in the compression estimate. -/
theorem sum_sourceErrorWeights {E : Type*} [Fintype E]
    (Q : ℝ) (k : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Finset E)).erase ∅,
      Q ^ S.card * (k : ℝ) ^ (-(S.card : ℝ) / 2)) =
      (1 + Q / Real.sqrt k) ^ Fintype.card E - 1 := by
  classical
  have h (n : ℕ) : (k : ℝ) ^ (-(n : ℝ) / 2) = ((Real.sqrt k)⁻¹) ^ n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg k),
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
    congr 1
    ring
  simp_rw [h, ← mul_pow, ← div_eq_mul_inv]
  exact sum_nonemptyFinsets_pow_card _

/-- An explicit positive sample count, with the zero-source case included.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 548–558. -/
def sourceSamplingCount (N : ℕ) (Q ε : ℝ) : ℕ :=
  ⌈(8 * (max 1 N : ℕ) * Q / ε) ^ 2⌉₊ + 1

/-- At least one sample is used. -/
theorem sourceSamplingCount_pos (N : ℕ) (Q ε : ℝ) :
    0 < sourceSamplingCount N Q ε := by
  unfold sourceSamplingCount
  omega

/-- The chosen count gives the required inverse-square-root error factor. -/
theorem div_sqrt_sourceSamplingCount_le (N : ℕ) (Q ε : ℝ)
    (hQ : 0 ≤ Q) (hε : 0 < ε) :
    Q / Real.sqrt (sourceSamplingCount N Q ε) ≤ ε / (8 * (max 1 N : ℕ)) := by
  let t := 8 * (max 1 N : ℕ) * Q / ε
  have ht : 0 ≤ t := by positivity
  have hk : 0 < (sourceSamplingCount N Q ε : ℝ) :=
    Nat.cast_pos.mpr (sourceSamplingCount_pos N Q ε)
  have ht2 : t ^ 2 ≤ (sourceSamplingCount N Q ε : ℝ) := by
    have h := Nat.le_ceil (t ^ 2)
    simp only [sourceSamplingCount, Nat.cast_add, Nat.cast_one]
    exact h.trans (le_add_of_nonneg_right zero_le_one)
  have hs : t ≤ Real.sqrt (sourceSamplingCount N Q ε) := by
    nlinarith [Real.sq_sqrt hk.le, Real.sqrt_nonneg (sourceSamplingCount N Q ε)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hk)).mpr
  have he : t * ε = 8 * (max 1 N : ℕ) * Q := by
    dsimp [t]
    field_simp
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (max 1 N : ℕ))).mpr
  have hmul := mul_le_mul_of_nonneg_right hs hε.le
  rw [he] at hmul
  simpa [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The integer rounding adds less than two to a quadratic bound. -/
theorem sourceSamplingCount_lt (N : ℕ) (Q ε : ℝ) :
    (sourceSamplingCount N Q ε : ℝ) < (8 * (max 1 N : ℕ) * Q / ε) ^ 2 + 2 := by
  have h := Nat.ceil_lt_add_one (sq_nonneg (8 * (max 1 N : ℕ) * Q / ε))
  simp only [sourceSamplingCount, Nat.cast_add, Nat.cast_one]
  linarith

open Classical in
/-- The subset sum is at most one quarter of the prescribed error for the
explicit sample count. No source terms are present when the index type is empty. -/
theorem sum_sourceErrorWeights_sourceSamplingCount_le {E : Type*} [Fintype E]
    (Q ε : ℝ) (hQ : 0 ≤ Q) (hε : 0 < ε) (hεone : ε ≤ 1) :
    (∑ S ∈ (Finset.univ : Finset (Finset E)).erase ∅,
      Q ^ S.card * (sourceSamplingCount (Fintype.card E) Q ε : ℝ) ^
        (-(S.card : ℝ) / 2)) ≤ ε / 4 := by
  rw [sum_sourceErrorWeights]
  let N := Fintype.card E
  let q := Q / Real.sqrt (sourceSamplingCount N Q ε)
  change (1 + q) ^ N - 1 ≤ ε / 4
  have hq : 0 ≤ q := by positivity
  have hqbound : q ≤ ε / (8 * (max 1 N : ℕ)) :=
    div_sqrt_sourceSamplingCount_le N Q ε hQ hε
  have hN : (N : ℝ) ≤ (max 1 N : ℕ) := by exact_mod_cast Nat.le_max_right 1 N
  have hmul : (N : ℝ) * q ≤ ε / 8 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (max 1 N : ℕ))).mp hqbound
    nlinarith [mul_le_mul_of_nonneg_right hN hq]
  have hpow : (1 + q) ^ N ≤ Real.exp ((N : ℝ) * q) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp q]) N
  have he := Real.abs_exp_sub_one_le (x := ε / 8) (by
    rw [abs_of_nonneg (by positivity)]
    linarith)
  rw [abs_of_nonneg (by positivity : 0 ≤ ε / 8)] at he
  have he' := (le_abs_self (Real.exp (ε / 8) - 1)).trans he
  have hexp := Real.exp_le_exp.mpr hmul
  linarith

end TNLean.PEPS.Approximation
