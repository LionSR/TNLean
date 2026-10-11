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
  done

end TNLean.PEPS.AreaLaw.Scan.ScannerExponents
