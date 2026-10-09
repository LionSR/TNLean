/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimension
import TNLean.PEPS.AreaLaw.Scan.RadiusAsymptotics

/-!
# Uniform physical transport coefficients and radius smallness

For the source radius `⌈Cr log² n⌉`, the physical transport cap is at most
`(1 + (2Cr+3)² log q) log⁴ n` once `log n ≥ 1`. Thus the constant and the
threshold are fixed before the domain, interaction labels, history, or scan.
Only the fixed physical dimension and radius coefficient enter the constant.

Two arbitrary real transport coefficients and exponents have a common
logarithmic-power bound on the full physical interval `1 ≤ ℓ ≤ ℓ_q(r₀)`.
The exponent is first enlarged to a nonnegative number, before increasing the
base. For positive radii, the manuscript's smallness assumption on `a r₀²`
also implies smallness of `a ℓ_q(r₀)`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 49 and 358–359, and `06-transport.tex`, lines 331–352,
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

/-- Two fixed transport coefficients admit one logarithmic-power bound,
chosen before the system size and every physical subsystem. The coefficients
and exponents may have either sign. The physical dimension and radius
coefficient remain fixed, as in `08-scanner.tex`, lines 49 and 358–359. -/
theorem exists_transportCoefficients_log_bound {q : ℕ} {Cr : ℝ}
    (hq : 1 ≤ q) (hCr : 0 ≤ Cr) (Cent eent Cen een : ℝ) :
    ∃ C Cl : ℝ, 1 ≤ C ∧ 0 ≤ Cl ∧ ∀ n : ℕ, 1 ≤ Real.log n →
      ∀ ℓ : ℝ, 1 ≤ ℓ → ℓ ≤ transportLogDimBound q (roundedLogRadius Cr n) →
        Cent * ℓ ^ eent ≤ C * (Real.log n) ^ Cl ∧
          Cen * ℓ ^ een ≤ C * (Real.log n) ^ Cl := by
  let E := max 0 (max eent een)
  let A := 1 + (2 * Cr + 3) ^ 2 * Real.log q
  let C := 1 + (|Cent| + |Cen|) * A ^ E
  have hE : 0 ≤ E := le_max_left _ _
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 1 ≤ C := by
    exact le_add_of_nonneg_right
      (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.rpow_nonneg hA E))
  refine ⟨C, 4 * E, hC, mul_nonneg (by norm_num) hE, ?_⟩
  intro n hn ℓ hℓ hcap
  have hn0 : 0 ≤ Real.log n := zero_le_one.trans hn
  have hℓ0 : 0 ≤ ℓ := zero_le_one.trans hℓ
  have hpower : ℓ ^ E ≤ A ^ E * (Real.log n) ^ (4 * E) := by
    calc
      _ ≤ (A * (Real.log n) ^ 4) ^ E := Real.rpow_le_rpow hℓ0
        (hcap.trans (transportLogDimBound_roundedLogRadius_le hq hCr hn)) hE
      _ = _ := by
        rw [Real.mul_rpow hA (pow_nonneg hn0 4), ← Real.rpow_natCast_mul hn0 4 E]
        norm_num
  have hbound (c e : ℝ) (hc : |c| ≤ |Cent| + |Cen|) (he : e ≤ E) :
      c * ℓ ^ e ≤ C * (Real.log n) ^ (4 * E) := by
    calc
      _ ≤ |c| * ℓ ^ e :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (Real.rpow_nonneg hℓ0 e)
      _ ≤ |c| * ℓ ^ E := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hℓ he) (abs_nonneg c)
      _ ≤ |c| * (A ^ E * (Real.log n) ^ (4 * E)) :=
        mul_le_mul_of_nonneg_left hpower (abs_nonneg c)
      _ = (|c| * A ^ E) * (Real.log n) ^ (4 * E) := by ring
      _ ≤ C * (Real.log n) ^ (4 * E) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0 _)
        exact (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hA E)).trans
          (le_add_of_nonneg_left zero_le_one)
  exact ⟨hbound Cent eent (le_add_of_nonneg_right (abs_nonneg _))
      ((le_max_left _ _).trans (le_max_right _ _)),
    hbound Cen een (le_add_of_nonneg_left (abs_nonneg _))
      ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- The physical logarithmic dimension is at most a fixed multiple of the
squared radius, provided the radius is positive. This is the conversion used
between `08-scanner.tex`, lines 358–359, and `06-transport.tex`, lines 331–350. -/
theorem transportLogDimBound_le_radius_sq {q r : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r) :
    transportLogDimBound q r ≤ (1 + 9 * Real.log q) * (r : ℝ) ^ 2 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr1
  have hside : 2 * (r : ℝ) + 1 ≤ 3 * (r : ℝ) := by linarith
  have hsquare : (2 * (r : ℝ) + 1) ^ 2 ≤ 9 * (r : ℝ) ^ 2 := by
    calc
      _ ≤ (3 * (r : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hside 2
      _ = _ := by ring
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  unfold transportLogDimBound
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hsquare hqlog]

/-- The manuscript's radius-smallness premise implies the transport
smallness premise with the explicit physical factor `1 + 9 log q`.
The nonnegativity of `a` and the positive-radius guard are retained. -/
theorem mul_transportLogDimBound_le_of_radius_small {q r : ℕ} {a c₀ : ℝ}
    (hq : 1 ≤ q) (hr : 1 ≤ r) (ha : 0 ≤ a)
    (hsmall : a * (r : ℝ) ^ 2 ≤ c₀ / (1 + 9 * Real.log q)) :
    a * transportLogDimBound q r ≤ c₀ := by
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hfactor : 0 < 1 + 9 * Real.log q := by positivity
  calc
    _ ≤ a * ((1 + 9 * Real.log q) * (r : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (transportLogDimBound_le_radius_sq hq hr) ha
    _ = (a * (r : ℝ) ^ 2) * (1 + 9 * Real.log q) := by ring
    _ ≤ c₀ := (le_div_iff₀ hfactor).mp hsmall

/-- A positive transport threshold gives a positive radius-smallness threshold
chosen before the radius, rate, system size, or scanner. -/
theorem exists_pos_radius_smallness_threshold {q : ℕ} {c₀ : ℝ}
    (hq : 1 ≤ q) (hc₀ : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 1 ≤ r → ∀ a : ℝ, 0 ≤ a →
      a * (r : ℝ) ^ 2 ≤ c → a * transportLogDimBound q r ≤ c₀ := by
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  refine ⟨c₀ / (1 + 9 * Real.log q), div_pos hc₀ (by positivity), ?_⟩
  intro r hr a ha hsmall
  exact mul_transportLogDimBound_le_of_radius_small hq hr ha hsmall

end TNLean.PEPS.AreaLaw.Scan
