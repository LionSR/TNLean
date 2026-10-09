/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadHistoryGeometricTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polynomial bounds for the finite bad-history tail

A fixed lower cutoff on ancestry length suffices once the actual charge ratio
is bounded by a negative power of the scale. Counting every remaining length
is deliberately coarser than summing an infinite geometric series, but its
polynomial loss does not affect arbitrary inverse-power decay.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 309–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

namespace CollarScan

variable {V I : Type*}

/-- A fixed ancestry cutoff converts a power bound on the actual ratio into a
finite tail bound, without extending the physical history space. -/
theorem geometricBadTail_le_power (S : CollarScan V I) (N multiplicity J : ℕ)
    {n : ℝ} {a : ℝ} (hn : 1 ≤ n) (ha : 0 ≤ a)
    (hcut : 4 * S.r₀ * J ≤ S.D)
    (hratio : S.badChargeRatio multiplicity ≤ n ^ (-a)) :
    S.geometricBadTail N multiplicity ≤ (N + 1 : ℕ) * n ^ (-a * J) := by
  have hq : 0 ≤ S.badChargeRatio multiplicity := by unfold badChargeRatio; positivity
  have hn0 : 0 ≤ n := le_trans zero_le_one hn
  have hp : n ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.mpr ha)
  unfold geometricBadTail
  calc
    _ ≤ ∑ _j ∈ (Finset.range (N + 1)).filter (fun j ↦ S.D < 4 * S.r₀ * j),
        n ^ (-a * J) := by
      apply Finset.sum_le_sum
      intro j hj
      have hJj : J ≤ j := by
        by_contra h
        have hh := Nat.mul_le_mul_left (4 * S.r₀) (Nat.le_of_lt (Nat.lt_of_not_ge h))
        exact (not_lt_of_ge (hh.trans hcut)) (Finset.mem_filter.mp hj).2
      calc
        _ ≤ (n ^ (-a)) ^ j := pow_le_pow_left₀ hq hratio j
        _ ≤ (n ^ (-a)) ^ J := pow_le_pow_of_le_one (Real.rpow_nonneg hn0 _) hp hJj
        _ = _ := (Real.rpow_mul_natCast hn0 (-a) J).symm
    _ ≤ (N + 1 : ℕ) * n ^ (-a * J) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0 _)
      exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- The complete finite time, band, endpoint, and length count has degree seven
at the source scales. -/
theorem badHistory_prefactor_le {K L m t n : ℕ} {Ct : ℝ}
    (hn : 1 ≤ n) (hK : K ≤ n) (hL : L ≤ n) (hm : m ≤ n)
    (hCt : 0 ≤ Ct) (ht : (t : ℝ) ≤ Ct * (n : ℝ) ^ 2) :
    ((K * 2 * (t + n * L) * (n * m + 1) : ℕ) : ℝ) * (n * m + 1 : ℕ) ≤
      8 * (Ct + 1) * (n : ℝ) ^ 7 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK' : (K : ℝ) ≤ n := by exact_mod_cast hK
  have hL' : (L : ℝ) ≤ n := by exact_mod_cast hL
  have hm' : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hnm : (n : ℝ) * m + 1 ≤ 2 * (n : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg n)]
  have htL : (t : ℝ) + n * L ≤ (Ct + 1) * (n : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL' (Nat.cast_nonneg n)]
  push_cast
  calc
    _ ≤ (n : ℝ) * 2 * ((Ct + 1) * (n : ℝ) ^ 2) *
        (2 * (n : ℝ) ^ 2) * (2 * (n : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

/-- Absorbing the polynomial prefactor requires only a fixed ancestry length.
The cutoff is chosen before the scale and the domain. -/
theorem badHistory_power_le {n a p Ct : ℝ} {J : ℕ}
    (hn : 1 ≤ n) (hc : 8 * (Ct + 1) ≤ n)
    (hJ : p + 8 ≤ a * J) :
    8 * (Ct + 1) * n ^ 7 * n ^ (-a * J) ≤ n ^ (-p) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  calc
    _ ≤ n * n ^ 7 * n ^ (-a * J) := by gcongr
    _ = n ^ ((8 : ℝ) + (-a * J)) := by
      rw [Real.rpow_add hn0, show (8 : ℝ) = (8 : ℕ) by norm_num, Real.rpow_natCast]
      ring
    _ ≤ n ^ (-p) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
