/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs

/-!
# Scale arithmetic and comparator budgets of the scan

Elementary consequences of the scales `scanner:scales`, and the comparator inputs of
Proposition 9.2: the transfer of the entropy input from `Ω` to `\widetilde Ω`, the shell budget
`B_sh ≤ C (n L^e + n)`, the mismatch budget `B_exc ≤ C n D`, the marginal parameter
`𝓑 ≤ C n D (log n)^C`, and the terminal rough upper bound `≤ C W n^{1+e}`.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.eventually_scaleFacts`
* `TNLean.PEPS.AreaLaw.Scan.ScanData.SXt_le`, `TNLean.PEPS.AreaLaw.Scan.ScanData.SQt_le`
* `TNLean.PEPS.AreaLaw.Scan.exists_budgets`

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  section file `08-scanner.tex`, lines 32–59 (scales), 386–391 (budgets in the statement of
  Proposition 9.2), 400–414 (entropy transfer and budgets), 462–470 (terminal bound).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open Filter

/-- The elementary scale facts hold for all sufficiently large `n` (`08-scanner.tex`,
lines 32–42, 469, 480, 519–520). -/
theorem eventually_scaleFacts (X : ScannerExponents) :
    ∃ C₁ : ℝ, ∀ᶠ n in atTop, ScaleFacts X n C₁ := by
  sorry

namespace ScanData

variable {X : ScannerExponents} {κ : ScanConstants}

/-- The truncation costs `O(n^{-248})` in the target entropy: the trace distance is
`O(n^{-500})` and the target has `O(n²)` sites (lines 400–403, Lemma 2.1). -/
theorem SXt_le (X : ScannerExponents) (κ : ScanConstants) :
    ∀ᶠ n in atTop, ∀ S : ScanData X κ n,
      S.SXt ≤ κ.Ce * (n : ℝ) ^ (1 + X.e) + (n : ℝ) ^ (-248 : ℝ) := by
  sorry

/-- The truncation costs `O(n^{-248})` in every shell entropy (lines 400–403, Lemma 2.1). -/
theorem SQt_le (X : ScannerExponents) (κ : ScanConstants) :
    ∀ᶠ n in atTop, ∀ S : ScanData X κ n, ∀ j ≤ X.L n,
      S.SQt j ≤ κ.Ce * (n * (X.L n : ℝ) ^ X.e + n) + (n : ℝ) ^ (-248 : ℝ) := by
  sorry

end ScanData

/-- The comparator budgets of Proposition 9.2 (lines 386–391, proof lines 400–410) and the
terminal rough upper bound (lines 462–470): for all sufficiently large `n`, uniformly in the
scan data, `B_sh ≤ C (n L^e + n)`, `B_exc ≤ C n D`, `𝓑 ≤ C n D (log n)^{C_l}`, and
`2 log d_* - log z + 2sW(2B_sh/z + 2B_exc) ≤ C W n^{1+e}`. -/
theorem exists_budgets (X : ScannerExponents) (κ : ScanConstants) :
    ∃ C Cl : ℝ, ∀ᶠ n in atTop, ∀ S : ScanData X κ n,
      S.Bsh ≤ C * (n * (X.L n : ℝ) ^ X.e + n) ∧
      S.Bexc ≤ C * n * X.D n ∧
      S.Bmarg ≤ C * n * X.D n * Real.log n ^ Cl ∧
      S.terminalBound ≤ C * X.W * (n : ℝ) ^ (1 + X.e) := by
  sorry

end TNLean.PEPS.AreaLaw.Scan
