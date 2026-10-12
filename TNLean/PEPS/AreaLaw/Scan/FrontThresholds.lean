/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SideSeparation

/-!
# Scanner fronts inside the original collar

The near comparison threshold is the lower band endpoint plus the number of
completed advances. The far threshold is the upper endpoint minus that number.
Throughout the fill horizon, both thresholds lie below the original collar depth.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:fronts`, lines 83–124, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

/-- Both positive-depth comparison thresholds stay below the original collar
depth throughout the fill horizon. Source: OpenAI area-law manuscript,
`08-scanner.tex`, `scanner:fronts`, lines 83–124, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem front_comparison_thresholds_le {V I : Type*}
    (S : CollarScan V I) (g : Fin S.K) (r : Fin S.m) {t L : ℕ}
    (hn : 0 < S.n) (ht : t ≤ S.n * S.m) (hL : 8 * S.K * S.m ≤ L) :
    S.front g r t false - 1 ≤ (L : ℤ) ∧
      -S.front g r t true ≤ (L : ℤ) := by
  have hupper := S.upper_le g r hL
  have hshift : ((fillCount t false / S.n : ℕ) : ℤ) ≤ (S.m : ℤ) := by
    exact_mod_cast fillCount_div_le_window hn ht false
  simp only [front, nominalFront, initialFront, lower, upper, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hupper ⊢
  have hfar : 0 ≤ ((fillCount t true / S.n : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

end TNLean.PEPS.AreaLaw.Scan.CollarScan
