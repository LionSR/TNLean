/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IndependentTruncationParameters

/-!
# Parameters for normalized ground-state approximation

The truncation threshold and the integer window are chosen before the
Hamiltonian and the target vector. The fourth-root window bound is retained
through the filter estimate and the logarithm of its polynomial-family count.
These estimates support ALVV, arXiv:1602.08828v2, Theorem 4.9, proof line 1080.

**Local fix (parameter choice):** The independent scales correct the printed
nonuniform prescription; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

namespace Real

/-- Squaring the elementary Chebyshev bound gives the numerical error used
by the viable-space enlargement. Auxiliary to ALVV, arXiv:1602.08828v2,
Theorem 4.2, item 3, and the proof of Theorem 4.9, line 1080. -/
theorem squared_chebyshev_error_eq (ell gap R : ℝ) :
    (2 * exp (-2 * ell ^ 2 * sqrt (gap / R))) ^ 2 =
      4 * exp (-4 * ell ^ 2 * sqrt (gap / R)) := by
  rw [mul_pow, ← exp_nat_mul]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num]
  congr 2
  ring

/-- A logarithmic accuracy variable at least sixteen makes the squared
filter error at most one eighth of the requested error. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem 4.9, proof line 1080. -/
theorem squared_chebyshev_error_le_accuracy
    (ell gap R a delta : ℝ) (hdelta : 0 < delta) (ha : 16 ≤ a)
    (haccuracy : log (1 / delta) ≤ a)
    (hexponent : a ≤ ell ^ 2 * sqrt (gap / R)) :
    (2 * exp (-2 * ell ^ 2 * sqrt (gap / R))) ^ 2 ≤ delta / 8 := by
  rw [squared_chebyshev_error_eq]
  have hexp : exp (-a) ≤ delta := by
    have hlog : -a ≤ log delta := by
      rw [one_div, log_inv] at haccuracy
      linarith only [haccuracy]
    simpa only [exp_log hdelta] using exp_le_exp.mpr hlog
  have hsmall : 4 * exp (-3 * a) ≤ 1 / 8 := by
    rw [show -3 * a = -(3 * a) by ring, exp_neg]
    change 4 / exp (3 * a) ≤ 1 / 8
    apply (div_le_iff₀ (exp_pos _)).2
    have he := add_one_le_exp (3 * a)
    nlinarith only [he, ha]
  calc
    _ ≤ 4 * exp (-4 * a) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hexponent]))
        (by norm_num)
    _ = (4 * exp (-3 * a)) * exp (-a) := by
      rw [show -4 * a = -3 * a + -a by ring, exp_add]
      ring
    _ ≤ (1 / 8) * delta :=
      mul_le_mul hsmall hexp (exp_nonneg _) (by norm_num)
    _ = delta / 8 := by ring

/-- One universal scalar choice gives both physical truncation accuracy and
an improving error proportional to the requested approximation accuracy.
The independent window retains the powers in ALVV, arXiv:1602.08828v2,
Theorem 4.9, proof line 1080. -/
theorem exists_sharp_approximation_scalar_parameters :
    ∃ C : ℝ, 21 ≤ C ∧
      ∀ g delta : ℝ, 0 < g → g ≤ 1 → 0 < delta → delta ≤ 1 →
      let a := 16 + log (1 / g) + log (1 / delta)
      let t := C * a
      ∃ ell : ℕ, 1 ≤ ell ∧
      (ell : ℝ) ≤ 8 / (4 * g / 5) +
        (7 * C) ^ (1 / 4 : ℝ) * (1 / (4 * g / 5)) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) ∧
      21 ≤ t ∧
      (288 * exp (11 / 8)) * exp (-(t - g) / 8) ≤ delta * g / 1000000 ∧
      ∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
        (2 * exp (-2 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R))) ^ 2 ≤ delta / 8 := by
  obtain ⟨C, hC, hthreshold⟩ := exists_independent_truncation_threshold_constant
  refine ⟨C, hC, ?_⟩
  intro g delta hg hg1 hdelta hdelta1 a t
  let u := 1 + log (1 / g) + log (1 / delta)
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hlogdelta : 0 ≤ log (1 / delta) := log_nonneg ((one_le_div hdelta).2 hdelta1)
  have ha : 16 ≤ a := by dsimp only [a]; linarith only [hlogg, hlogdelta]
  have hau : u ≤ a := by dsimp only [a, u]; linarith
  have hCu : C * u ≤ t := by
    change C * u ≤ C * a
    exact mul_le_mul_of_nonneg_left hau (by linarith only [hC])
  obtain ⟨ht, htail⟩ := hthreshold g delta hg hg1 hdelta hdelta1
  have htail' : (288 * exp (11 / 8)) * exp (-(t - g) / 8) ≤
      delta * g / 1000000 := by
    refine le_trans ?_ htail
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr
    change -(t - g) / 8 ≤ -(C * u - g) / 8
    linarith only [hCu]
  obtain ⟨ell, hell, hbound, hfilter⟩ :=
    exists_quarter_power_truncation_filter_scale C (4 * g / 5) a
      (by linarith only [hC]) (by linarith only [hg]) (by linarith only [hg1])
      (by linarith only [ha])
  refine ⟨ell, hell, hbound, ht.trans hCu, htail', ?_⟩
  intro R hR hRbudget
  exact squared_chebyshev_error_le_accuracy (ell : ℝ) (4 * g / 5) R a delta
    hdelta ha (by dsimp only [a]; linarith only [hlogg]) (hfilter R hR hRbudget)

end Real
