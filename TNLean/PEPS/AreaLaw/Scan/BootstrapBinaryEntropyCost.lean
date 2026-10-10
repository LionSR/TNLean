/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Budgets
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Binary-entropy cost for the rounded bootstrap bands

For each fixed tuple of scanner exponents, one large-scale threshold gives
positive band count and positive per-band metric weight. With total metric
weight four, the binary-entropy cost is at most `(log 2 / 4) n` above that
threshold. The coefficient is absolute; the threshold may depend on the
fixed exponent tuple and precedes every auxiliary fraction and physical
instance.

The proof uses the actual rounded bands `K = floor(L / (8m))` and the
existing scale estimates `1 ≤ K` and `L ≤ n`, together with `h(τ) ≤ log 2`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `08-scanner.tex`, `scanner:scales`, lines 32–41, and
the binary-entropy cost following `scanner:bootstrap-comparison`,
lines 755–787, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- For fixed scanner exponents, one threshold gives positive actual band
count, positive per-band weight, and a linear binary-entropy cost with
absolute coefficient. The threshold precedes the auxiliary fraction and
every physical instance. Source: `08-scanner.tex`, `scanner:scales`,
lines 32–41, and the cost following `scanner:bootstrap-comparison`,
lines 755–787. -/
theorem exists_bootstrap_binaryEntropy_cost_bound (X : ScannerExponents) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 ≤ X.K n ∧ 0 < X.a 4 n ∧ ∀ τ : ℝ,
        Real.binEntropy τ / X.a 4 n ≤ (Real.log 2 / 4) * (n : ℝ) := by
  obtain ⟨C₁, hscale⟩ := eventually_scaleFacts X
  obtain ⟨N, hN⟩ := hscale.exists_forall_of_atTop
  refine ⟨N, (le_trans (by norm_num : (1 : ℕ) ≤ 2) (hN N le_rfl).two_le_n),
    fun n hn ↦ ?_⟩
  have hfacts := hN n hn
  have hKpos : (0 : ℝ) < X.K n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfacts.one_le_K)
  have ha : 0 < X.a 4 n :=
    div_pos (by norm_num : (0 : ℝ) < 4) hKpos
  have hKbound : (X.K n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.div_le_self (X.L n) (8 * X.m n)).trans hfacts.L_le_n
  have hcoefficient : 0 ≤ Real.log 2 / 4 :=
    div_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
      (by norm_num : (0 : ℝ) ≤ 4)
  refine ⟨hfacts.one_le_K, ha, fun τ ↦ ?_⟩
  calc
    Real.binEntropy τ / X.a 4 n =
        (Real.binEntropy τ / 4) * (X.K n : ℝ) := by
      rw [ScannerExponents.a, div_div_eq_mul_div]
      ring
    _ ≤ (Real.log 2 / 4) * (X.K n : ℝ) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right Real.binEntropy_le_log_two
          (by norm_num : (0 : ℝ) ≤ 4)) (Nat.cast_nonneg (X.K n))
    _ ≤ (Real.log 2 / 4) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hKbound hcoefficient

end TNLean.PEPS.AreaLaw.Scan
