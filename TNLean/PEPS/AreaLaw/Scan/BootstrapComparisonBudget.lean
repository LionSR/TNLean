/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapParameters
import TNLean.PEPS.AreaLaw.Scan.BootstrapBinaryEntropyCost

/-!
# The additive entropy budget for the fixed bootstrap scales

Fix an initial exponent between the final box exponent and one. The parameters
of the scan are chosen from this initial exponent. One large-scale threshold,
chosen before the current exponent and the auxiliary fraction, bounds the sum
of the shell, separation, typical-window and binary-entropy costs by the
improved power, with absolute coefficient `5 + log 2 / 4`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `08-scanner.tex`, `scanner:scales`, lines 32–41,
`scanner:bootstrap-parameters`, lines 693–703, and the estimates following
`scanner:bootstrap-comparison`, lines 755–787, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The statement is independently formulated from the manuscript; no upstream Lean proof
text is reused.

-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The complete numerical comparison budget is bounded at one threshold
depending on the initial exponent, before the current exponent or auxiliary
fraction is selected. The floors, ceiling and band weight are the scales of
`scanner:scales`; the separation exponent is fixed throughout the bootstrap.
Source: `08-scanner.tex`, lines 32–41, 693–703 and 755–787. -/
theorem exists_bootstrap_comparison_budget_bound {e₀ : ℝ}
    (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let η : ℝ := 1 - BootstrapParameters.ell e₀
      let L : ℕ := Nat.floor ((n : ℝ) ^ η)
      let m : ℕ := Nat.floor ((n : ℝ) ^ BootstrapParameters.mu e₀)
      let K : ℕ := L / (8 * m)
      let D : ℕ := Nat.ceil ((n : ℝ) ^ BootstrapParameters.kappa e₀)
      let a : ℝ := 4 / (K : ℝ)
      1 ≤ K ∧ 0 < a ∧
        ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
          ∀ τ : ℝ,
            (n : ℝ) * (L : ℝ) ^ e + (n : ℝ) * (D : ℝ) +
                (n : ℝ) ^ (3 / 5 : ℝ) + Real.binEntropy τ / a + 1 ≤
              (5 + Real.log 2 / 4) * (n : ℝ) ^ (1 + η * e) := by
  have he₀pos : 0 < e₀ := lt_trans (by norm_num [Exponents.boxError]) he₀
  obtain ⟨hg₀, hg₀half, hℓ, hℓ₁, hκ⟩ :=
    BootstrapParameters.parameter_bounds he₀pos he₀₁
  have hℓg₀ : BootstrapParameters.ell e₀ < BootstrapParameters.g0 e₀ :=
    (div_lt_self (div_pos hg₀ (by norm_num : (0 : ℝ) < 1000))
      (by norm_num : (1 : ℝ) < 100)).trans
      (div_lt_self hg₀ (by norm_num : (1 : ℝ) < 1000))
  have hμℓ : BootstrapParameters.mu e₀ < 1 - BootstrapParameters.ell e₀ :=
    sub_lt_sub_left hℓg₀ 1
  have hκμ : BootstrapParameters.kappa e₀ < BootstrapParameters.mu e₀ := by
    linarith [show BootstrapParameters.kappa e₀ ≤ BootstrapParameters.ell e₀ from
      min_le_left _ _, show BootstrapParameters.mu e₀ = 1 - BootstrapParameters.g0 e₀ from rfl]
  let X : ScannerExponents :=
    { ell := BootstrapParameters.ell e₀
      kappa := BootstrapParameters.kappa e₀
      mu := BootstrapParameters.mu e₀
      nu := BootstrapParameters.nu e₀
      e := e₀
      ell_pos := hℓ
      ell_lt_one := hℓ₁
      kappa_pos := hκ
      kappa_lt_mu := hκμ
      mu_lt_one_sub_ell := hμℓ
      nu_pos := div_pos hg₀ (by norm_num)
      e_pos := he₀pos
      e_lt_one := he₀₁
      kappa_le_e :=
        (show BootstrapParameters.kappa e₀ ≤
            (Exponents.boxError : ℝ) / 4 from min_le_right _ _).trans
          ((show (Exponents.boxError : ℝ) / 4 ≤
              (Exponents.boxError : ℝ) by norm_num [Exponents.boxError]).trans he₀.le) }
  obtain ⟨N, hN, hcost⟩ := exists_bootstrap_binEntropy_cost_bound X
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  refine ⟨(hcost n hn).1, (hcost n hn).2.1, fun e he hee₀ τ ↦ ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hN.trans hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hepos : 0 < e := lt_trans (by norm_num [Exponents.boxError]) he
  -- Everything is compared against the improved power `n ^ (1 + (1 - ℓ) e)`.
  change (n : ℝ) * (X.L n : ℝ) ^ e + (n : ℝ) * (X.D n : ℝ) + (n : ℝ) ^ (3 / 5 : ℝ)
      + Real.binEntropy τ / X.a 4 n + 1
      ≤ (5 + Real.log 2 / 4) * (n : ℝ) ^ (1 + (1 - X.ell) * e)
  have hmul : (n : ℝ) ^ (1 + (1 - X.ell) * e)
      = (n : ℝ) * (n : ℝ) ^ ((1 - X.ell) * e) := by
    rw [Real.rpow_add hnpos, Real.rpow_one]
  -- The collar depth `L ≤ n^{1-ℓ}`, so `L^e ≤ n^{(1-ℓ)e}`.
  have hLle : (X.L n : ℝ) ≤ (n : ℝ) ^ (1 - X.ell) := Nat.floor_le (by positivity)
  have hLe : (X.L n : ℝ) ^ e ≤ (n : ℝ) ^ ((1 - X.ell) * e) :=
    calc (X.L n : ℝ) ^ e ≤ ((n : ℝ) ^ (1 - X.ell)) ^ e :=
          Real.rpow_le_rpow (by positivity) hLle hepos.le
      _ = (n : ℝ) ^ ((1 - X.ell) * e) := by rw [← Real.rpow_mul hnpos.le]
  have ht1 : (n : ℝ) * (X.L n : ℝ) ^ e ≤ (n : ℝ) ^ (1 + (1 - X.ell) * e) := by
    rw [hmul]; exact mul_le_mul_of_nonneg_left hLe hnpos.le
  -- The separation exponent `κ < (1 - ℓ) e`, so `n D ≤ 2 n^{1 + (1-ℓ)e}`.
  have hκlt : X.kappa < (1 - X.ell) * e :=
    (BootstrapParameters.comparison_exponents he₀pos he).1
  have hκ1 : (1 : ℝ) ≤ (n : ℝ) ^ X.kappa := Real.one_le_rpow hn1 X.kappa_pos.le
  have hDceil : (X.D n : ℝ) ≤ (n : ℝ) ^ X.kappa + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hDn : (n : ℝ) ^ X.kappa ≤ (n : ℝ) ^ ((1 - X.ell) * e) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hκlt.le
  have hD2 : (X.D n : ℝ) ≤ 2 * (n : ℝ) ^ ((1 - X.ell) * e) :=
    calc (X.D n : ℝ) ≤ (n : ℝ) ^ X.kappa + 1 := hDceil
      _ ≤ 2 * (n : ℝ) ^ X.kappa := by linarith
      _ ≤ 2 * (n : ℝ) ^ ((1 - X.ell) * e) := by linarith
  have ht2 : (n : ℝ) * (X.D n : ℝ) ≤ 2 * (n : ℝ) ^ (1 + (1 - X.ell) * e) := by
    rw [hmul]
    calc (n : ℝ) * (X.D n : ℝ)
        ≤ (n : ℝ) * (2 * (n : ℝ) ^ ((1 - X.ell) * e)) :=
          mul_le_mul_of_nonneg_left hD2 hnpos.le
      _ = 2 * ((n : ℝ) * (n : ℝ) ^ ((1 - X.ell) * e)) := by ring
  -- The improved power dominates `1`, `n` and the typical width `n^{3/5}`.
  have hP1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 + (1 - X.ell) * e) :=
    Real.one_le_rpow hn1 (by linarith)
  have hPn : (n : ℝ) ≤ (n : ℝ) ^ (1 + (1 - X.ell) * e) :=
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ (1 + (1 - X.ell) * e) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have ht3 : (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (1 + (1 - X.ell) * e) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  -- The binary-entropy cost contributes the single `log 2 / 4` coefficient.
  have hlog0 : (0 : ℝ) ≤ Real.log 2 / 4 :=
    div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have ht4 : Real.binEntropy τ / X.a 4 n
      ≤ (Real.log 2 / 4) * (n : ℝ) ^ (1 + (1 - X.ell) * e) :=
    ((hcost n hn).2.2 τ).trans (mul_le_mul_of_nonneg_left hPn hlog0)
  have hdistrib : (5 + Real.log 2 / 4) * (n : ℝ) ^ (1 + (1 - X.ell) * e)
      = 5 * (n : ℝ) ^ (1 + (1 - X.ell) * e)
        + (Real.log 2 / 4) * (n : ℝ) ^ (1 + (1 - X.ell) * e) := by ring
  linarith [ht1, ht2, ht3, ht4, hP1, hdistrib]

end TNLean.PEPS.AreaLaw.Scan
