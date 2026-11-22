/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.Truncation.IndependentTruncationParameters

/-!
# Parameters for normalized ground-state approximation

The truncation threshold and the integer window are chosen before the
Hamiltonian and the target vector. The fourth-root window bound is retained
through the filter estimate and the logarithm of its polynomial-family count.
These estimates support ALVV, arXiv:1602.08828v2, Theorem 4.9, proof line 1080.

**Local fix (parameter choice):** The independent scales correct the printed
nonuniform prescription; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.

## Independent sharp approximation scales at a fixed low-energy bandwidth

The original-to-clipped spectral comparison needs a residual proportional
to the square of the energy buffer. The existing independent-threshold
estimate is applied at the squared buffer and a bandwidth-adjusted accuracy.
This changes only fixed-bandwidth constants. The integer window retains the
fourth-root buffer and three-quarter-power accuracy dependence.

This numerical auxiliary supports ALVV, arXiv:1602.08828v2, Theorem
`thm:al-ld`, lines 1096–1105, and the buffered improving family at
lines 1027–1041. It does not assume or construct physical filter operators.
The scalar buffer is positive and capped at one; the physical construction
will derive that cap from its actual narrower width.
-/

section

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

end

section

namespace Real

/-- A fixed-bandwidth choice of independent clipping threshold and polynomial
window gives both the squared-buffer residual budget and the sharp Chebyshev
accuracy. The constant is chosen before the buffer and requested error.
ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_sharp_low_density_scalar_parameters (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 21 ≤ C ∧
      ∀ g delta : ℝ, 0 < g → g ≤ 1 → 0 < delta → delta ≤ 1 →
      let a := 16 + log (1 / g) + log (1 / delta)
      let t := C * a
      ∃ ell : ℕ, 1 ≤ ell ∧
      (ell : ℝ) ≤ 8 / g +
        (7 * C) ^ (1 / 4 : ℝ) * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) ∧
      19 + eta ≤ t ∧
      (288 * exp (11 / 8)) * exp (-(t - eta) / 8) ≤ 1 ∧
      2 * (6 + eta) * ((288 * exp (11 / 8)) * exp (-(t - eta) / 8)) ≤
        (delta / 100) * g ^ 2 ∧
      ∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
        (2 * exp (-2 * (ell : ℝ) ^ 2 * sqrt (g / R))) ^ 2 ≤ delta / 8 := by
  obtain ⟨C0, hC0, hthreshold⟩ := exists_independent_truncation_threshold_constant
  let B := 6 + eta
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [heta]
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hlogB : 0 ≤ log B := log_nonneg hB
  let C := eta + C0 * (2 + log B)
  have hC : 21 ≤ C := by
    have hmul := mul_nonneg (by linarith only [hC0] : 0 ≤ C0) hlogB
    dsimp only [C]
    nlinarith only [hC0, hmul, heta]
  refine ⟨C, hC, ?_⟩
  intro g delta hg hg1 hdelta hdelta1 a t
  let tau := delta / B
  let u := 1 + log (1 / (g ^ 2)) + log (1 / tau)
  have htau : 0 < tau := div_pos hdelta hBpos
  have htau1 : tau ≤ 1 :=
    (div_le_iff₀ hBpos).mpr (by simpa only [one_mul] using hdelta1.trans hB)
  have hgsq : 0 < g ^ 2 := sq_pos_of_pos hg
  have hgsq1 : g ^ 2 ≤ 1 := by nlinarith only [hg, hg1]
  obtain ⟨ht0, htail0⟩ := hthreshold (g ^ 2) tau hgsq hgsq1 htau htau1
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hlogdelta : 0 ≤ log (1 / delta) :=
    log_nonneg ((one_le_div hdelta).mpr hdelta1)
  have ha : 16 ≤ a := by dsimp only [a]; linarith only [hlogg, hlogdelta]
  have hu : u = 1 + 2 * log (1 / g) + log B + log (1 / delta) := by
    simp only [u, tau, one_div, log_inv, log_pow, log_div hdelta.ne' hBpos.ne']
    norm_num only [Nat.cast_ofNat]
    ring
  have hscale : u ≤ (2 + log B) * a := by
    have hm := mul_nonneg hlogB (by linarith only [ha] : 0 ≤ a - 1)
    rw [hu]
    dsimp only [a] at ha ⊢
    nlinarith only [hm, hlogg, hlogdelta]
  have ht : eta + C0 * u ≤ t := by
    have hm := mul_le_mul_of_nonneg_left hscale
      (by linarith only [hC0] : 0 ≤ C0)
    have he := mul_nonneg heta.le (by linarith only [ha] : 0 ≤ a - 1)
    dsimp only [t, C]
    nlinarith only [hm, he]
  let xi := (288 * exp (11 / 8)) * exp (-(t - eta) / 8)
  have hxi : 0 ≤ xi := by dsimp only [xi]; positivity
  have htail : xi ≤ tau * g ^ 2 / 1000000 := by
    refine le_trans ?_ htail0
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr
    change -(t - eta) / 8 ≤ -(C0 * u - g ^ 2) / 8
    linarith only [ht, hgsq]
  have hxi1 : xi ≤ 1 := by
    have hp : tau * g ^ 2 ≤ 1 :=
      (mul_le_mul htau1 hgsq1 (sq_nonneg g) (by norm_num)).trans (by norm_num)
    have := htail.trans (div_le_div_of_nonneg_right hp (by norm_num))
    linarith only [this]
  have hsmall : 2 * (6 + eta) * xi ≤ (delta / 100) * g ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 2 * B)
    have hc : 2 * B * (tau * g ^ 2 / 1000000) = delta * g ^ 2 / 500000 := by
      dsimp only [tau]
      field_simp
      ring
    rw [hc] at hm
    change 2 * B * xi ≤ (delta / 100) * g ^ 2
    have hp := mul_nonneg hdelta.le (sq_nonneg g)
    linarith only [hm, hp]
  obtain ⟨ell, hell, hbound, hfilter⟩ :=
    exists_quarter_power_truncation_filter_scale C g a
      ((by norm_num : (1 : ℝ) ≤ 21).trans hC) hg hg1 (by linarith only [ha])
  refine ⟨ell, hell, hbound, ?_, hxi1, hsmall, ?_⟩
  · linarith only [ht, ht0]
  · intro R hR hRbudget
    exact squared_chebyshev_error_le_accuracy (ell : ℝ) g R a delta
      hdelta ha (by dsimp only [a]; linarith only [hlogg]) (hfilter R hR hRbudget)

end Real

end
