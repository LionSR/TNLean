/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Budgets
import TNLean.PEPS.AreaLaw.RegionalEntropyContinuity

/-!
# Target entropy transfer for the same quantitative truncation

The regional continuity bound and the actual target-window trace distance
give a uniform `n^(-247)` entropy discrepancy on every region of controlled
quadratic volume. Both vectors and the region are supplied. The threshold
precedes all finite physical data and every later entropy bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 399–404; Lemma 2.1 in `01-preliminaries.tex`, lines 33–46,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- The same actual trace-distance estimate controls the target entropy,
uniformly over all regions of the supplied quadratic volume bound.
Source: `08-scanner.tex`, lines 399–404. -/
theorem eventually_abs_regionalEntropy_sub_le_of_truncation
    (q : ℕ) (hq : 1 ≤ q) (g Cvol : ℝ) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (Λ : Finset (ℤ × ℤ)) (Ω Ωt : StateSpace Λ q),
      ‖Ω‖ = 1 → ‖Ωt‖ = 1 → ∀ X : Finset (Site Λ),
      (X.card : ℝ) ≤ Cvol * (n : ℝ) ^ 2 →
      Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
          (Matrix.vecMulVec Ω (star Ω)) ≤
        Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) →
      |regionalEntropy Λ q Ωt X - regionalEntropy Λ q Ω X| ≤
        (n : ℝ) ^ (-247 : ℝ) := by
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have key := eventually_continuityCost_le_of_fixed_coefficient
    (Real.sqrt (2 / g)) (max 4 Cvol) (Real.log q)
    (Real.sqrt_nonneg _) (le_trans (by norm_num) (le_max_left _ _)) hlq
  filter_upwards [key] with n hcost Λ Ω Ωt hΩ hΩt X hcard hdist
  set t := Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
    (Matrix.vecMulVec Ω (star Ω)) with ht
  have hhalf : Real.sqrt ((n : ℝ) ^ (-1000 : ℝ)) = (n : ℝ) ^ (-500 : ℝ) := by
    have h1 : (n : ℝ) ^ (-1000 : ℝ) = ((n : ℝ) ^ (-500 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-500 : ℝ)) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 1
      norm_num
    rw [h1, Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  have htbound : t ≤ Real.sqrt (2 / g) * (n : ℝ) ^ (-500 : ℝ) := by
    refine hdist.trans ?_
    have hmin : min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) ≤ (n : ℝ) ^ (-1000 : ℝ) := min_le_left _ _
    have h2g : (0 : ℝ) ≤ 2 / g := div_nonneg (by norm_num) hg.le
    have hle : 2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g ≤ 2 * (n : ℝ) ^ (-1000 : ℝ) / g := by
      rw [show 2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g
            = (2 / g) * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) by ring,
        show 2 * (n : ℝ) ^ (-1000 : ℝ) / g = (2 / g) * (n : ℝ) ^ (-1000 : ℝ) by ring]
      exact mul_le_mul_of_nonneg_left hmin h2g
    calc Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g)
        ≤ Real.sqrt (2 * (n : ℝ) ^ (-1000 : ℝ) / g) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (2 / g) * (n : ℝ) ^ (-500 : ℝ) := by
          rw [show 2 * (n : ℝ) ^ (-1000 : ℝ) / g = (2 / g) * (n : ℝ) ^ (-1000 : ℝ) by ring,
            Real.sqrt_mul h2g, hhalf]
  have hcard' : (X.card : ℝ) ≤ (max 4 Cvol) * (n : ℝ) ^ 2 :=
    hcard.trans (mul_le_mul_of_nonneg_right (le_max_right 4 Cvol) (sq_nonneg _))
  have hcont := abs_regionalEntropy_sub_le_sqrt_traceDistance Λ q Ωt Ω hΩt hΩ X
  refine hcont.trans ?_
  calc
    4 * Real.sqrt t * (1 + (X.card : ℝ) * Real.log q) ≤
        (max 4 Cvol) * Real.sqrt t *
          (1 + (max 4 Cvol) * (n : ℝ) ^ 2 * Real.log q) := by
      gcongr <;> first | exact le_max_left 4 Cvol | exact hcard'
    _ ≤ (n : ℝ) ^ (-247 : ℝ) := hcost t htbound

end TNLean.PEPS.AreaLaw.Scan
