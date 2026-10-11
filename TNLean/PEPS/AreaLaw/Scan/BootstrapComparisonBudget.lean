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

**Proof status:** The statement has been elaborated; its proof is under construction.
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
  done

end TNLean.PEPS.AreaLaw.Scan
