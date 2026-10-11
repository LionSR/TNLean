/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimension
import TNLean.PEPS.AreaLaw.Scan.RadiusAsymptotics

/-!
# Uniform logarithmic-fourth-power transport dimension bound

For the source radius `⌈Cr log² n⌉`, the physical transport cap is at most
`(1 + (2Cr+3)² log q) log⁴ n` once `log n ≥ 1`. Thus the constant and the
threshold are fixed before the domain, interaction labels, history, or scan.
Only the fixed physical dimension and radius coefficient enter the constant.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, line 49, and `06-transport.tex`, lines 331–352,
at `openai/math@adc7f124`.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- The source squared-logarithmic radius gives a fourth-power logarithmic cap,
with an explicit constant and no geometry-dependent parameters. -/
theorem transportLogDimBound_roundedLogRadius_le {q n : ℕ} {Cr : ℝ}
    (hq : 1 ≤ q) (hCr : 0 ≤ Cr) (hlog : 1 ≤ Real.log n) :
    transportLogDimBound q (roundedLogRadius Cr n) ≤
      (1 + (2 * Cr + 3) ^ 2 * Real.log q) * (Real.log n) ^ 4 := by
  have hl2 : 1 ≤ (Real.log n) ^ 2 := one_le_pow₀ hlog
  have hl4 : 1 ≤ (Real.log n) ^ 4 := one_le_pow₀ hlog
  have hr : (roundedLogRadius Cr n : ℝ) ≤ Cr * (Real.log n) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hCr (sq_nonneg _))).le
  have hside : 2 * (roundedLogRadius Cr n : ℝ) + 1 ≤
      (2 * Cr + 3) * (Real.log n) ^ 2 := by nlinarith
  have hsquare : (2 * (roundedLogRadius Cr n : ℝ) + 1) ^ 2 ≤
      (2 * Cr + 3) ^ 2 * (Real.log n) ^ 4 := by
    calc
      _ ≤ ((2 * Cr + 3) * (Real.log n) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hside 2
      _ = _ := by ring
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  unfold transportLogDimBound
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hsquare hqlog]

/-- The eventual cap is selected before any finite physical system. Its
coefficient depends only on `q` and `Cr`; no eventual estimate is an input. -/
theorem eventually_transportLogDimBound_roundedLogRadius_le {q : ℕ} {Cr : ℝ}
    (hq : 1 ≤ q) (hCr : 0 ≤ Cr) :
    ∀ᶠ n : ℕ in atTop, transportLogDimBound q (roundedLogRadius Cr n) ≤
      (1 + (2 * Cr + 3) ^ 2 * Real.log q) * (Real.log n) ^ 4 := by
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hlog] with n hn
  exact transportLogDimBound_roundedLogRadius_le hq hCr hn

/-- There is a positive fixed coefficient for the source-scale physical cap.
The quantifiers choose it and its threshold before every actual scanner. -/
theorem exists_transportLogDimBound_log_four {q : ℕ} {Cr : ℝ}
    (hq : 1 ≤ q) (hCr : 0 ≤ Cr) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      transportLogDimBound q (roundedLogRadius Cr n) ≤ C * (Real.log n) ^ 4 := by
  refine ⟨1 + (2 * Cr + 3) ^ 2 * Real.log q, ?_,
    eventually_transportLogDimBound_roundedLogRadius_le hq hCr⟩
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  positivity

end TNLean.PEPS.AreaLaw.Scan
