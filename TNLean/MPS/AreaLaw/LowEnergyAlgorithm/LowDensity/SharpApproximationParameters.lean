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

It also contains the following results.

* `Real.sharp_polynomial_family_log_count`, `Real.sharp_approximation_log_rank_budget`: logarithmic
  counts at the independent approximation scales.
-/

section SharpApproximationParameters

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

end SharpApproximationParameters

section SharpRankCount

/-!
## Logarithmic counts at the independent approximation scales

The exact polynomial-family count is estimated without replacing its
fourth-root window by the coarser entropy scale. These estimates support
ALVV, arXiv:1602.08828v2, Theorem 4.9, proof line 1080.
-/

namespace Real

/-- The logarithm of the actual polynomial-family count retains the
quarter-power gap and three-quarter-power accuracy terms of its window.
The additional factor is logarithmic in the logarithmic accuracy variable.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem 4.9, proof line 1080. -/
theorem sharp_polynomial_family_log_count
    (q ell : ℕ) (g a b : ℝ) (hq : 1 ≤ q) (hell : 1 ≤ ell)
    (hg : 0 < g) (hg1 : g ≤ 1) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hwindow : (ell : ℝ) ≤ 10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    log (((q * ell ^ 2) ^ (22 * ell) : ℕ) : ℝ) ≤
      44 * (1 + log (11 + b)) *
        (10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) *
        u * (1 + log a) := by
  intro u
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hellpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast (by omega : 0 < ell)
  have hapos : 0 < a := zero_lt_one.trans_le ha
  have hinv : 1 ≤ 1 / g := (one_le_div hg).2 hg1
  have hinvpos : 0 < 1 / g := one_div_pos.mpr hg
  have hrootg : (1 / g) ^ (1 / 4 : ℝ) ≤ 1 / g := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hinv (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hroota : a ^ (3 / 4 : ℝ) ≤ a := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le ha (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hproduct : (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) ≤ (1 / g) * a :=
    mul_le_mul hrootg hroota (rpow_nonneg hapos.le _) hinvpos.le
  have hcoarse : (ell : ℝ) ≤ (11 + b) * (1 / g) * a := by
    calc
      (ell : ℝ) ≤ 10 / g + b *
          ((1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) := by
        simpa only [mul_assoc] using hwindow
      _ ≤ 10 / g + b * ((1 / g) * a) :=
        by linarith only [mul_le_mul_of_nonneg_left hproduct hb]
      _ = 10 * (1 / g) + b * ((1 / g) * a) := by ring
      _ ≤ (11 + b) * (1 / g) * a := by
        have hten := mul_le_mul_of_nonneg_left ha (show 0 ≤ 10 * (1 / g) by positivity)
        nlinarith only [hten, mul_nonneg hinvpos.le hapos.le]
  have hKpos : 0 < 11 + b := by linarith only [hb]
  have hlogK : 0 ≤ log (11 + b) := log_nonneg (by linarith only [hb])
  have hlogell : log (ell : ℝ) ≤ log (11 + b) + log (1 / g) + log a := by
    have h := log_le_log hellpos hcoarse
    rw [log_mul (mul_pos hKpos hinvpos).ne' hapos.ne', log_mul hKpos.ne' hinvpos.ne'] at h
    exact h
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast hq)
  have hlogg : 0 ≤ log (1 / g) := log_nonneg hinv
  have hloga : 0 ≤ log a := log_nonneg ha
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  have hlogbase : log (q : ℝ) + 2 * log (ell : ℝ) ≤
      2 * (1 + log (11 + b)) * u * (1 + log a) := by
    have huEq : u = 1 + log (q : ℝ) + log (1 / g) := rfl
    have hfirst : log (q : ℝ) + 2 * log (ell : ℝ) ≤
        2 * (1 + log (11 + b)) * (u + log a) := by
      nlinarith only [hlogell, huEq, hlogq,
        mul_nonneg hlogK (sub_nonneg.mpr hu), mul_nonneg hlogK hloga]
    have hlast : u + log a ≤ u * (1 + log a) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hu) hloga]
    calc
      _ ≤ 2 * (1 + log (11 + b)) * (u + log a) := hfirst
      _ ≤ 2 * (1 + log (11 + b)) * (u * (1 + log a)) :=
        mul_le_mul_of_nonneg_left hlast (by positivity)
      _ = _ := by ring
  have hidentity : log (((q * ell ^ 2) ^ (22 * ell) : ℕ) : ℝ) =
      22 * (ell : ℝ) * (log (q : ℝ) + 2 * log (ell : ℝ)) := by
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, log_pow]
    rw [log_mul hqpos.ne' (pow_pos hellpos 2).ne', log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [hidentity]
  calc
    _ ≤ 22 * (ell : ℝ) * (2 * (1 + log (11 + b)) * u * (1 + log a)) :=
      mul_le_mul_of_nonneg_left hlogbase (by positivity)
    _ = (44 * (1 + log (11 + b)) * u * (1 + log a)) * (ell : ℝ) := by ring
    _ ≤ (44 * (1 + log (11 + b)) * u * (1 + log a)) *
        (10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hwindow (by positivity)
    _ = _ := by ring

/-- A bootstrap count and the independent polynomial count give a logarithmic
rank budget with coefficient one on the logarithm of the target dimension.
The only additional accuracy factor is `1 + log a`. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem 4.9, fixed-cut rank estimate. -/
theorem sharp_approximation_log_rank_budget
    (r D0 q ell : ℕ) (g a K0 b : ℝ)
    (hr : 1 ≤ r) (hD0 : 1 ≤ D0) (hq : 1 ≤ q) (hell : 1 ≤ ell)
    (hg : 0 < g) (hg1 : g ≤ 1) (ha : 1 ≤ a) (hK0 : 0 ≤ K0) (hb : 0 ≤ b)
    (hwindow : (ell : ℝ) ≤ 10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ))
    (hbootstrap : log (D0 : ℝ) ≤ K0 / g *
      (1 + log (q : ℝ) + log (1 / g)) ^ 3) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    let D1 : ℕ := (q * ell ^ 2) ^ (22 * ell)
    log ((r * D0 ^ 24 * D1 ^ 2 : ℕ) : ℝ) ≤ log (r : ℝ) +
      (24 * K0 + 88 * (1 + log (11 + b)) * (11 + b)) *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) * (1 + log a) := by
  intro u D1
  let X := u ^ 3 / g
  let Y := (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u
  let P := 1 + log a
  let kappa := 44 * (1 + log (11 + b))
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast hq)
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hloga : 0 ≤ log a := log_nonneg ha
  have hP : 1 ≤ P := by dsimp only [P]; linarith only [hloga]
  have hkappa : 0 ≤ kappa := by
    have hlogb : 0 ≤ log (11 + b) := log_nonneg (by linarith only [hb])
    dsimp only [kappa]
    positivity
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hucube : u ≤ u ^ 3 := by
    have hu2 : 1 ≤ u ^ 2 := by nlinarith only [hu]
    nlinarith only [mul_le_mul_of_nonneg_left hu2 hu0]
  have huX : u / g ≤ X := div_le_div_of_nonneg_right hucube hg.le
  have hcount : log (D1 : ℝ) ≤ kappa *
      (10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) * u * P :=
    sharp_polynomial_family_log_count q ell g a b hq hell hg hg1 ha hb hwindow
  have hcountpoly :
      (10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) * u ≤
        (11 + b) * (X + Y) := by
    calc
      _ = 10 * (u / g) + b * Y := by dsimp only [Y]; ring
      _ ≤ 10 * X + b * Y := by linarith only [huX]
      _ ≤ (11 + b) * (X + Y) := by
        nlinarith only [hX, hY, mul_nonneg hb hX]
  have hcountgrow : 2 * log (D1 : ℝ) ≤
      2 * kappa * (11 + b) * (X + Y) * P := by
    have hscale := mul_le_mul_of_nonneg_left hcountpoly hkappa
    have hscaleP := mul_le_mul_of_nonneg_right hscale (zero_le_one.trans hP)
    nlinarith only [hcount, hscaleP]
  have hXgrow : X ≤ (X + Y) * P := by
    nlinarith only [hY, mul_nonneg (add_nonneg hX hY) (sub_nonneg.mpr hP)]
  have hbasegrow : 24 * log (D0 : ℝ) ≤ 24 * K0 * (X + Y) * P := by
    have hbase : log (D0 : ℝ) ≤ K0 * X := by
      calc
        _ ≤ K0 / g * u ^ 3 := hbootstrap
        _ = K0 * X := by dsimp only [X]; ring
    have hscale := mul_le_mul_of_nonneg_left hXgrow hK0
    nlinarith only [hbase, hscale]
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hD0pos : (0 : ℝ) < (D0 : ℝ) := by exact_mod_cast (by omega : 0 < D0)
  have hD1posN : 0 < D1 := by dsimp only [D1]; positivity
  have hD1pos : (0 : ℝ) < (D1 : ℝ) := by exact_mod_cast hD1posN
  have hidentity : log ((r * D0 ^ 24 * D1 ^ 2 : ℕ) : ℝ) =
      log (r : ℝ) + 24 * log (D0 : ℝ) + 2 * log (D1 : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [log_mul (mul_pos hrpos (pow_pos hD0pos 24)).ne' (pow_pos hD1pos 2).ne',
      log_mul hrpos.ne' (pow_pos hD0pos 24).ne', log_pow, log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [hidentity]
  calc
    _ ≤ log (r : ℝ) + 24 * K0 * (X + Y) * P +
        2 * kappa * (11 + b) * (X + Y) * P := by
      linarith only [hbasegrow, hcountgrow]
    _ = _ := by dsimp only [X, Y, P, kappa]; ring

end Real

end SharpRankCount
