/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceSamplingCount

/-!
# Polynomial bounds for the explicit source sample count

The number of original source occurrences, the choice-cost bound, and the
inverse target accuracy determine an explicit power bound for the integer
sample count. All coefficients and exponents in the conclusion depend only on
the corresponding uniform bounds, never on private dimensions or source ranks.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 174–175,
269–277, 364–369 and 548–558.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-polynomial-bounds; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-actual-sampling-sourcesamplingpolynomial-01
TNLean.PEPS.Approximation.sourceSamplingCount_lt_inv_pow
Provenance-ID: 8769-actual-sampling-sourcesamplingpolynomial-02
TNLean.PEPS.Approximation.sourceSamplingCount_lt_of_gate_power_bounds
Provenance-ID: 8769-actual-sampling-sourcesamplingpolynomial-03
TNLean.PEPS.Approximation.sourceSamplingCount_lt_of_power_bounds
-/


noncomputable section
namespace TNLean.PEPS.Approximation

/-- Power bounds for the number of sources, the choice cost, and inverse accuracy
give a uniform power bound for the explicit integer sample count. -/
theorem sourceSamplingCount_lt_of_power_bounds (N : ℕ) (Q ε L : ℝ)
    (C_N C_Q C_ε : ℝ) (n q p : ℕ)
    (hL : 1 ≤ L) (hCN : 1 ≤ C_N) (hCQ : 0 ≤ C_Q)
    (hQ : 0 ≤ Q) (hε : 0 < ε)
    (hN : (N : ℝ) ≤ C_N * L ^ n) (hQbound : Q ≤ C_Q * L ^ q)
    (hεbound : ε⁻¹ ≤ C_ε * L ^ p) :
    (sourceSamplingCount N Q ε : ℝ) <
      (64 * C_N ^ 2 * C_Q ^ 2 * C_ε ^ 2 + 2) * L ^ (2 * (n + q + p)) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hNmax : ((max 1 N : ℕ) : ℝ) ≤ C_N * L ^ n := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (one_le_mul_of_one_le_of_one_le hCN (one_le_pow₀ hL)) hN
  have ht : 8 * (max 1 N : ℕ) * Q / ε ≤
      8 * (C_N * L ^ n) * (C_Q * L ^ q) * (C_ε * L ^ p) := by
    rw [div_eq_mul_inv]
    gcongr
  have ht' : 8 * (max 1 N : ℕ) * Q / ε ≤
      (8 * C_N * C_Q * C_ε) * L ^ (n + q + p) := by
    convert ht using 1
    simp only [pow_add]
    ring
  have hs : (8 * (max 1 N : ℕ) * Q / ε) ^ 2 ≤
      ((8 * C_N * C_Q * C_ε) * L ^ (n + q + p)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) ht' 2
  have he : ((8 * C_N * C_Q * C_ε) * L ^ (n + q + p)) ^ 2 =
      (64 * C_N ^ 2 * C_Q ^ 2 * C_ε ^ 2) * L ^ (2 * (n + q + p)) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (n + q + p) 2]
    ring
  rw [he] at hs
  have hLp : 1 ≤ L ^ (2 * (n + q + p)) := one_le_pow₀ hL
  have hk := sourceSamplingCount_lt N Q ε
  nlinarith

/-- At inverse-power accuracy, the sample-count exponent is twice the sum of
the source-count exponent, the choice-cost exponent, and the accuracy exponent. -/
theorem sourceSamplingCount_lt_inv_pow (N : ℕ) (Q L C_N C_Q : ℝ)
    (n q p : ℕ) (hL : 1 ≤ L) (hCN : 1 ≤ C_N) (hCQ : 0 ≤ C_Q)
    (hQ : 0 ≤ Q) (hN : (N : ℝ) ≤ C_N * L ^ n) (hQbound : Q ≤ C_Q * L ^ q) :
    (sourceSamplingCount N Q (L ^ p)⁻¹ : ℝ) <
      (64 * C_N ^ 2 * C_Q ^ 2 + 2) * L ^ (2 * (n + q + p)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  simpa only [one_pow, mul_one] using sourceSamplingCount_lt_of_power_bounds
    N Q (L ^ p)⁻¹ L C_N C_Q 1 n q p hL hCN hCQ hQ (by positivity)
    hN hQbound (by simp)

/-- With the manuscript's choice cost `B^(4b) D^4`, power bounds for gate
coefficients and local physical dimensions give an explicit polynomial sample count.
The exponent depends on the fixed participation bound and the prescribed accuracy,
and the coefficient is independent of all private dimensions and source ranks. -/
theorem sourceSamplingCount_lt_of_gate_power_bounds (N b : ℕ)
    (B D L C_N C_B C_D : ℝ) (n m r p : ℕ)
    (hL : 1 ≤ L) (hCN : 1 ≤ C_N) (hCB : 0 ≤ C_B)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hN : (N : ℝ) ≤ C_N * L ^ n)
    (hBbound : B ≤ C_B * L ^ m) (hDbound : D ≤ C_D * L ^ r) :
    (sourceSamplingCount N (B ^ (4 * b) * D ^ 4) (L ^ p)⁻¹ : ℝ) <
      (64 * C_N ^ 2 * (C_B ^ (4 * b) * C_D ^ 4) ^ 2 + 2) *
        L ^ (2 * (n + 4 * b * m + 4 * r + p)) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hQbound : B ^ (4 * b) * D ^ 4 ≤
      (C_B ^ (4 * b) * C_D ^ 4) * L ^ (4 * b * m + 4 * r) := by
    calc
      _ ≤ (C_B * L ^ m) ^ (4 * b) * (C_D * L ^ r) ^ 4 := by gcongr
      _ = _ := by
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm m (4 * b), Nat.mul_comm r 4, pow_add]
        ring
  simpa only [Nat.add_assoc] using sourceSamplingCount_lt_inv_pow
    N (B ^ (4 * b) * D ^ 4) L C_N (C_B ^ (4 * b) * C_D ^ 4)
    n (4 * b * m + 4 * r) p hL hCN (by positivity) (by positivity) hN hQbound

end TNLean.PEPS.Approximation
