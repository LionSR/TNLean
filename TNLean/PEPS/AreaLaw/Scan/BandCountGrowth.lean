/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Budgets

/-!
# Growth of the rounded scanner band count

The collar depth grows faster than the window scale. Consequently, the actual
rounded band count eventually exceeds every fixed integer. The threshold depends
only on the exponents and that integer, before any physical system or scan is chosen.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, `08-scanner.tex`, `scanner:scales`, lines 32–41, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  The argument is independently written from the manuscript; no upstream Lean
  proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan.ScannerExponents

open Filter

/-- Every fixed lower bound on the band count holds at all sufficiently large
scales. The band count retains both floors and the integer division of
`08-scanner.tex`, `scanner:scales`, lines 32–41. -/
theorem eventually_le_K (X : ScannerExponents) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, B ≤ X.K n := by
  have hgap : 0 < 1 - X.ell - X.mu := sub_pos.mpr X.mu_lt_one_sub_ell
  have hμ : 0 < X.mu := X.kappa_pos.trans X.kappa_lt_mu
  have hℓ : 0 < 1 - X.ell := sub_pos.2 X.ell_lt_one
  filter_upwards [eventually_ge_atTop 1, eventually_le_natCast_rpow hμ 2,
    eventually_le_natCast_rpow hℓ 2, eventually_le_natCast_rpow hgap (16 * B)]
    with n hn hm hL hB
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hμn : (0 : ℝ) ≤ (n : ℝ) ^ X.mu := by positivity
  have hm_le : (X.m n : ℝ) ≤ (n : ℝ) ^ X.mu := Nat.floor_le hμn
  have hm_ge : (n : ℝ) ^ X.mu / 2 ≤ X.m n := half_le_floor hm
  have hL_ge : (n : ℝ) ^ (1 - X.ell) / 2 ≤ X.L n := half_le_floor hL
  have hm_pos : 0 < X.m n := by exact_mod_cast (show (0 : ℝ) < X.m n by linarith)
  have hsplit : (n : ℝ) ^ (1 - X.ell) = (n : ℝ) ^ (1 - X.ell - X.mu) * (n : ℝ) ^ X.mu := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hreal : (B : ℝ) * (8 * X.m n) ≤ X.L n := by
    have h1 : (B : ℝ) * (8 * X.m n) ≤ (B : ℝ) * (8 * (n : ℝ) ^ X.mu) := by gcongr
    have h2 := mul_le_mul_of_nonneg_right hB hμn
    nlinarith
  unfold ScannerExponents.K
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact_mod_cast hreal

end TNLean.PEPS.AreaLaw.Scan.ScannerExponents
