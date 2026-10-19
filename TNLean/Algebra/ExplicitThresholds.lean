/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit thresholds for elementary limits

Many estimates of the form "for all sufficiently large `n`" compare
elementary functions: a power against a larger power, a power of a logarithm
against a power, or a power against a stretched exponential. This file gives,
for each such comparison, a closed-form threshold beyond which the inequality
holds, so that a bound can be stated with a named lower scale instead of being
extracted from a limit.

## Main definitions and results

* `Real.powerRatioThreshold C η d = max 1 ((C / η) ^ (1 / d))`; beyond it
  `C x ^ a ≤ η x ^ b` whenever `b - a = d > 0`
  (`Real.mul_rpow_le_mul_rpow_of_powerRatioThreshold_le`).
* `Real.logPowThreshold C η a k`; beyond it `C (log x) ^ k ≤ η x ^ a` for
  `a > 0` (`Real.mul_log_pow_le_mul_rpow_of_logPowThreshold_le`).
* `Real.logRpowThreshold C η u v L`; beyond it `C x ^ u (log x) ^ L ≤ η x ^ v` for
  `u < v` and real `L`
  (`Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_logRpowThreshold_le`).
* `Real.stretchedExpThreshold C c θ s`; beyond it `C x ^ s ≤ exp (c x ^ θ)`
  for `c, θ > 0` (`Real.mul_rpow_le_exp_of_stretchedExpThreshold_le`), and
  equivalently `C exp (-(c x ^ θ)) ≤ x ^ (-s)`.
* `Real.le_rpow_of_powerRatioThreshold_le`: `b ≤ x ^ y` for `y > 0` beyond
  `powerRatioThreshold (max b 0) 1 y`; for natural arguments the threshold is
  `Real.natRpowThreshold y b`.
* `Real.add_mul_rpow_le_mul_rpow_of_le`: a two-term power sum is at most
  `η x ^ b` beyond the larger of two power-ratio thresholds.
* `Real.one_le_log_natCast_of_three_le`: `1 ≤ log n` for natural `n ≥ 3`.
* `Nat.half_le_floor_of_one_le`: `x / 2 ≤ ⌊x⌋₊` for `x ≥ 1`.

Each threshold result also has a form for natural arguments `n` with
`⌈threshold⌉₊ ≤ n`.

These lemmas serve the explicit value of the constant in Theorem 1.1 of the
two-dimensional area-law manuscript (OpenAI, *A two-dimensional area law from
a global spectral gap*, September 24, 2026, `00-introduction.tex`, lines
39–53). Its proof uses "sufficiently large `n`" thresholds of exactly these
shapes (`08-scanner.tex`, lines 198, 215, 412, 739, 817, 849;
`09-amplification.tex`, lines 274 and 499; `10-geometry.tex`, lines 206, 335,
380 and 760–774), and the source never quantifies them. The thresholds here
make each such step explicit. Ceilings of powers are already handled by
`Nat.ceil_le_two_mul` and `Nat.ceil_le_add_one_mul_of_le_mul`.
-/

open scoped Nat

namespace Real

/-- The explicit threshold `max 1 ((C / η) ^ (1 / d))` beyond which a power is
dominated by a power larger by `d`: `C x ^ a ≤ η x ^ (a + d)`. -/
noncomputable def powerRatioThreshold (C η d : ℝ) : ℝ :=
  max 1 ((C / η) ^ (1 / d))

/-- The power-ratio threshold is at least one. -/
theorem one_le_powerRatioThreshold (C η d : ℝ) : 1 ≤ powerRatioThreshold C η d :=
  le_max_left _ _

/-- **Power ratio with an explicit threshold.** If `0 ≤ C`, `0 < η` and `a < b`, then
`C x ^ a ≤ η x ^ b` for every `x ≥ max 1 ((C / η) ^ (1 / (b - a)))`. -/
theorem mul_rpow_le_mul_rpow_of_powerRatioThreshold_le {C η a b x : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η) (hab : a < b)
    (hx : powerRatioThreshold C η (b - a) ≤ x) :
    C * x ^ a ≤ η * x ^ b := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hx0 : 0 < x := one_pos.trans_le ((one_le_powerRatioThreshold _ _ _).trans hx)
  have hroot : (C / η) ^ (1 / (b - a)) ≤ x := (le_max_right _ _).trans hx
  have hCη : C / η ≤ x ^ (b - a) :=
    calc C / η = ((C / η) ^ (1 / (b - a))) ^ (b - a) := by
          rw [one_div, rpow_inv_rpow (div_nonneg hC hη.le) hd.ne']
      _ ≤ x ^ (b - a) := rpow_le_rpow (by positivity) hroot hd.le
  have hC' : C ≤ η * x ^ (b - a) := (div_le_iff₀' hη).mp hCη
  calc C * x ^ a ≤ η * x ^ (b - a) * x ^ a :=
        mul_le_mul_of_nonneg_right hC' (rpow_nonneg hx0.le _)
    _ = η * x ^ b := by rw [mul_assoc, ← rpow_add hx0, sub_add_cancel]

/-- Natural-number form of `mul_rpow_le_mul_rpow_of_powerRatioThreshold_le`:
`C n ^ a ≤ η n ^ b` for every `n ≥ ⌈powerRatioThreshold C η (b - a)⌉₊`. -/
theorem mul_rpow_le_mul_rpow_of_ceil_powerRatioThreshold_le {C η a b : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hη : 0 < η) (hab : a < b)
    (hn : ⌈powerRatioThreshold C η (b - a)⌉₊ ≤ n) :
    C * (n : ℝ) ^ a ≤ η * (n : ℝ) ^ b :=
  mul_rpow_le_mul_rpow_of_powerRatioThreshold_le hC hη hab (Nat.ceil_le.mp hn)

/-- **A positive power exceeds a constant, with an explicit threshold.** If `0 < y`, then
`b ≤ x ^ y` for every `x ≥ powerRatioThreshold (max b 0) 1 y = max 1 (max b 0 ^ (1 / y))`. -/
theorem le_rpow_of_powerRatioThreshold_le {b y x : ℝ} (hy : 0 < y)
    (hx : powerRatioThreshold (max b 0) 1 y ≤ x) : b ≤ x ^ y := by
  have h := mul_rpow_le_mul_rpow_of_powerRatioThreshold_le (x := x) (le_max_right b 0) one_pos hy
    (by rwa [sub_zero])
  rw [rpow_zero, mul_one, one_mul] at h
  exact (le_max_left b 0).trans h

/-- The natural threshold `⌈max 1 (max b 0 ^ (1 / y))⌉₊` beyond which `b ≤ n ^ y`. -/
noncomputable def natRpowThreshold (y b : ℝ) : ℕ :=
  ⌈powerRatioThreshold (max b 0) 1 y⌉₊

/-- The natural power threshold is at least one. -/
theorem one_le_natRpowThreshold (y b : ℝ) : 1 ≤ natRpowThreshold y b :=
  Nat.one_le_ceil_iff.mpr (one_pos.trans_le (one_le_powerRatioThreshold _ _ _))

/-- Natural-number form of `le_rpow_of_powerRatioThreshold_le`:
`b ≤ n ^ y` for every `n ≥ natRpowThreshold y b`. -/
theorem le_natCast_rpow_of_natRpowThreshold_le {b y : ℝ} {n : ℕ} (hy : 0 < y)
    (hn : natRpowThreshold y b ≤ n) : b ≤ (n : ℝ) ^ y :=
  le_rpow_of_powerRatioThreshold_le hy (Nat.ceil_le.mp hn)

/-- **Two-term power sum.** If `0 ≤ C₁, C₂`, `0 < η` and `a₁, a₂ < b`, then
`C₁ x ^ a₁ + C₂ x ^ a₂ ≤ η x ^ b` beyond the larger of the two power-ratio
thresholds at `η / 2`. -/
theorem add_mul_rpow_le_mul_rpow_of_le {C₁ C₂ η a₁ a₂ b x : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η) (ha₁ : a₁ < b) (ha₂ : a₂ < b)
    (hx : max (powerRatioThreshold C₁ (η / 2) (b - a₁))
      (powerRatioThreshold C₂ (η / 2) (b - a₂)) ≤ x) :
    C₁ * x ^ a₁ + C₂ * x ^ a₂ ≤ η * x ^ b := by
  have h₁ := mul_rpow_le_mul_rpow_of_powerRatioThreshold_le hC₁ (half_pos hη) ha₁
    ((le_max_left _ _).trans hx)
  have h₂ := mul_rpow_le_mul_rpow_of_powerRatioThreshold_le hC₂ (half_pos hη) ha₂
    ((le_max_right _ _).trans hx)
  linarith

/-- The exponent `a / (2 (k + 1))` used to compare `(log x) ^ k` with `x ^ (a / 2)`
through `log x ≤ x ^ ε / ε`. -/
noncomputable def logPowRate (a : ℝ) (k : ℕ) : ℝ :=
  a / (2 * (k + 1))

/-- The rate `logPowRate a k` is positive when `a` is. -/
theorem logPowRate_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < logPowRate a k := by
  unfold logPowRate; positivity

/-- The explicit threshold beyond which `C (log x) ^ k ≤ η x ^ a`: the power-ratio
threshold for `(C / ε ^ k) x ^ (a / 2) ≤ η x ^ a`, where `ε = a / (2 (k + 1))`. -/
noncomputable def logPowThreshold (C η a : ℝ) (k : ℕ) : ℝ :=
  powerRatioThreshold (C / logPowRate a k ^ k) η (a - a / 2)

/-- For `x ≥ 1` and `a > 0`, `(log x) ^ k ≤ x ^ (a / 2) / ε ^ k` with
`ε = a / (2 (k + 1))`. -/
theorem log_pow_le_rpow_div_logPowRate_pow {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x) (k : ℕ) :
    log x ^ k ≤ x ^ (a / 2) / logPowRate a k ^ k := by
  have hε := logPowRate_pos ha k
  have hx0 : 0 < x := one_pos.trans_le hx
  have hlog : log x ≤ x ^ logPowRate a k / logPowRate a k :=
    log_le_rpow_div hx0.le hε
  have hexp : logPowRate a k * k ≤ a / 2 := by
    unfold logPowRate
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  calc log x ^ k ≤ (x ^ logPowRate a k / logPowRate a k) ^ k :=
        pow_le_pow_left₀ (log_nonneg hx) hlog k
    _ = x ^ (logPowRate a k * k) / logPowRate a k ^ k := by
        rw [div_pow, rpow_mul_natCast hx0.le]
    _ ≤ x ^ (a / 2) / logPowRate a k ^ k := by
        gcongr

/-- **Powers of a logarithm against a power, with an explicit threshold.** If
`0 ≤ C`, `0 < η` and `0 < a`, then `C (log x) ^ k ≤ η x ^ a` for every
`x ≥ logPowThreshold C η a k`. -/
theorem mul_log_pow_le_mul_rpow_of_logPowThreshold_le {C η a x : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hη : 0 < η) (ha : 0 < a) (hx : logPowThreshold C η a k ≤ x) :
    C * log x ^ k ≤ η * x ^ a := by
  have hε := logPowRate_pos ha k
  have hx1 : 1 ≤ x := (one_le_powerRatioThreshold _ _ _).trans hx
  have hmain := mul_rpow_le_mul_rpow_of_powerRatioThreshold_le
    (div_nonneg hC (pow_nonneg hε.le k)) hη (half_lt_self ha) hx
  calc C * log x ^ k ≤ C * (x ^ (a / 2) / logPowRate a k ^ k) :=
        mul_le_mul_of_nonneg_left (log_pow_le_rpow_div_logPowRate_pow ha hx1 k) hC
    _ = C / logPowRate a k ^ k * x ^ (a / 2) := by ring
    _ ≤ η * x ^ a := hmain

/-- Natural-number form of `mul_log_pow_le_mul_rpow_of_logPowThreshold_le`. -/
theorem mul_log_pow_le_mul_rpow_of_ceil_logPowThreshold_le {C η a : ℝ} {k n : ℕ}
    (hC : 0 ≤ C) (hη : 0 < η) (ha : 0 < a) (hn : ⌈logPowThreshold C η a k⌉₊ ≤ n) :
    C * log (n : ℝ) ^ k ≤ η * (n : ℝ) ^ a :=
  mul_log_pow_le_mul_rpow_of_logPowThreshold_le hC hη ha (Nat.ceil_le.mp hn)

/-- The explicit threshold `max e (logPowThreshold C η (v - u) ⌈L⌉₊)` beyond which
`C x ^ u (log x) ^ L ≤ η x ^ v` for `u < v` and a real exponent `L`. -/
noncomputable def logRpowThreshold (C η u v L : ℝ) : ℝ :=
  max (exp 1) (logPowThreshold C η (v - u) ⌈L⌉₊)

/-- The threshold `logRpowThreshold C η u v L` exceeds `2`. -/
theorem two_lt_logRpowThreshold (C η u v L : ℝ) : 2 < logRpowThreshold C η u v L :=
  (by linarith [add_one_lt_exp one_ne_zero] : (2 : ℝ) < exp 1).trans_le (le_max_left _ _)

/-- **A power times a real power of a logarithm against a larger power, with an explicit
threshold.** If `0 ≤ C`, `0 < η` and `u < v`, then `C x ^ u (log x) ^ L ≤ η x ^ v` for every
`x ≥ logRpowThreshold C η u v L`, for every real exponent `L`. -/
theorem mul_rpow_mul_log_rpow_le_mul_rpow_of_logRpowThreshold_le {C η u v L x : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η) (huv : u < v) (hx : logRpowThreshold C η u v L ≤ x) :
    C * x ^ u * log x ^ L ≤ η * x ^ v := by
  have he : exp 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := (exp_pos 1).trans_le he
  have hlog : 1 ≤ log x := (log_exp 1).symm.le.trans (log_le_log (exp_pos 1) he)
  have hk : log x ^ L ≤ log x ^ ⌈L⌉₊ := by
    rw [← rpow_natCast]
    exact rpow_le_rpow_of_exponent_le hlog (Nat.le_ceil L)
  have hmain := mul_log_pow_le_mul_rpow_of_logPowThreshold_le hC hη (sub_pos.2 huv)
    ((le_max_right _ _).trans hx)
  calc C * x ^ u * log x ^ L = (C * log x ^ L) * x ^ u := by ring
    _ ≤ (C * log x ^ ⌈L⌉₊) * x ^ u := by gcongr
    _ ≤ (η * x ^ (v - u)) * x ^ u := by gcongr
    _ = η * x ^ v := by rw [mul_assoc, ← rpow_add hx0, sub_add_cancel]

/-- Natural-number form of `mul_rpow_mul_log_rpow_le_mul_rpow_of_logRpowThreshold_le`. -/
theorem mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le {C η u v L : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hη : 0 < η) (huv : u < v) (hn : ⌈logRpowThreshold C η u v L⌉₊ ≤ n) :
    C * (n : ℝ) ^ u * log (n : ℝ) ^ L ≤ η * (n : ℝ) ^ v :=
  mul_rpow_mul_log_rpow_le_mul_rpow_of_logRpowThreshold_le hC hη huv (Nat.ceil_le.mp hn)

/-- Every `n` from `⌈logRpowThreshold C η u v L⌉₊` on has `1 ≤ log n`. -/
theorem one_le_log_of_ceil_logRpowThreshold_le {C η u v L : ℝ} {n : ℕ}
    (hn : ⌈logRpowThreshold C η u v L⌉₊ ≤ n) : 1 ≤ log (n : ℝ) := by
  rw [le_log_iff_exp_le (by linarith [two_lt_logRpowThreshold C η u v L, Nat.ceil_le.mp hn])]
  exact (le_max_left _ _).trans (Nat.ceil_le.mp hn)

/-- Every natural number `n ≥ 3` has `log n ≥ 1`, since `e < 3`. -/
theorem one_le_log_natCast_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    1 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hn)

/-- Every `n` from `⌈logRpowThreshold C η u v L⌉₊` on is at least `2`. -/
theorem two_le_of_ceil_logRpowThreshold_le {C η u v L : ℝ} {n : ℕ}
    (hn : ⌈logRpowThreshold C η u v L⌉₊ ≤ n) : 2 ≤ n := by
  exact_mod_cast (two_lt_logRpowThreshold C η u v L).le.trans (Nat.ceil_le.mp hn)

/-- The number of Taylor terms `⌊s / θ⌋₊ + 1` used to compare `x ^ s` with
`exp (c x ^ θ)`; it satisfies `s < θ m`. -/
noncomputable def stretchedExpOrder (θ s : ℝ) : ℕ :=
  ⌊s / θ⌋₊ + 1

/-- The order `m = ⌊s / θ⌋₊ + 1` satisfies `s < θ m` when `θ > 0`. -/
theorem lt_mul_stretchedExpOrder {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    s < θ * stretchedExpOrder θ s := by
  have h : s / θ < stretchedExpOrder θ s := by
    unfold stretchedExpOrder
    exact_mod_cast Nat.lt_floor_add_one (s / θ)
  rw [div_lt_iff₀ hθ] at h
  linarith

/-- The explicit threshold beyond which `C x ^ s ≤ exp (c x ^ θ)`: with
`m = ⌊s / θ⌋₊ + 1`, the power-ratio threshold for `C x ^ s ≤ (c ^ m / m!) x ^ (θ m)`. -/
noncomputable def stretchedExpThreshold (C c θ s : ℝ) : ℝ :=
  powerRatioThreshold C (c ^ stretchedExpOrder θ s / (stretchedExpOrder θ s)!)
    (θ * stretchedExpOrder θ s - s)

/-- **A stretched exponential dominates every power, with an explicit threshold.**
If `0 ≤ C`, `0 < c` and `0 < θ`, then `C x ^ s ≤ exp (c x ^ θ)` for every
`x ≥ stretchedExpThreshold C c θ s`. -/
theorem mul_rpow_le_exp_of_stretchedExpThreshold_le {C c θ s x : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hθ : 0 < θ) (hx : stretchedExpThreshold C c θ s ≤ x) :
    C * x ^ s ≤ exp (c * x ^ θ) := by
  set m := stretchedExpOrder θ s
  have hx0 : 0 < x := one_pos.trans_le ((one_le_powerRatioThreshold _ _ _).trans hx)
  have hη : 0 < c ^ m / (m ! : ℝ) := by positivity
  have hmain := mul_rpow_le_mul_rpow_of_powerRatioThreshold_le hC hη
    (lt_mul_stretchedExpOrder hθ s) hx
  calc C * x ^ s ≤ c ^ m / (m ! : ℝ) * x ^ (θ * m) := hmain
    _ = (c * x ^ θ) ^ m / (m ! : ℝ) := by
        rw [rpow_mul_natCast hx0.le, mul_pow]; ring
    _ ≤ exp (c * x ^ θ) := pow_div_factorial_le_exp _ (by positivity) m

/-- Decay form of `mul_rpow_le_exp_of_stretchedExpThreshold_le`:
`C exp (-(c x ^ θ)) ≤ x ^ (-s)` for every `x ≥ stretchedExpThreshold C c θ s`. -/
theorem mul_exp_neg_le_rpow_neg_of_stretchedExpThreshold_le {C c θ s x : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hθ : 0 < θ) (hx : stretchedExpThreshold C c θ s ≤ x) :
    C * exp (-(c * x ^ θ)) ≤ x ^ (-s) := by
  have hx0 : 0 < x := one_pos.trans_le ((one_le_powerRatioThreshold _ _ _).trans hx)
  have h := mul_rpow_le_exp_of_stretchedExpThreshold_le hC hc hθ hx
  rw [rpow_neg hx0.le, exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _), inv_mul_eq_div,
    le_div_iff₀ (rpow_pos_of_pos hx0 s)]
  exact h

/-- Natural-number form of `mul_exp_neg_le_rpow_neg_of_stretchedExpThreshold_le`. -/
theorem mul_exp_neg_le_rpow_neg_of_ceil_stretchedExpThreshold_le {C c θ s : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hc : 0 < c) (hθ : 0 < θ) (hn : ⌈stretchedExpThreshold C c θ s⌉₊ ≤ n) :
    C * exp (-(c * (n : ℝ) ^ θ)) ≤ (n : ℝ) ^ (-s) :=
  mul_exp_neg_le_rpow_neg_of_stretchedExpThreshold_le hC hc hθ (Nat.ceil_le.mp hn)

end Real

namespace Nat

/-- The floor of a real number at least one is at least half of it. -/
theorem half_le_floor_of_one_le {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ ⌊x⌋₊ := by
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff x).mpr hx
  have h2 := Nat.lt_floor_add_one x
  linarith

end Nat
