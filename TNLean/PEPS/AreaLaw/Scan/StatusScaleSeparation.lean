/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.RadiusAsymptotics

/-!
# Literal rounded scales for the physical status estimates

For fixed exponents 0 < κ < μ, the rounded squared-logarithmic radius is
at most D = ceil(n^κ), and 4D is at most m = floor(n^μ), eventually in n.
The inequality 8Km ≤ L follows directly from K = L / (8m), including m = 0.
The threshold is chosen after the fixed exponents and radius coefficient,
but before every physical instance. No uniform threshold over unrestricted
positive exponent gaps is asserted. The thresholds are given explicitly by
`statusScaleSeparationThreshold` and `sourceBandCountThreshold`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32–58, at `openai/math@adc7f124`.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- The floor defining the number of bands always gives the literal collar bound. -/
theorem eight_mul_bandCount_mul_le (L m : ℕ) :
    8 * (L / (8 * m)) * m ≤ L := by
  calc
    _ = (L / (8 * m)) * (8 * m) := by ring
    _ ≤ L := Nat.div_mul_le_self L (8 * m)

/-- If `n^(μ-κ) ≥ 2c` with `n ≥ 1` and `κ ≥ 0`, then `c ⌈n^κ⌉ ≤ ⌊n^μ⌋`: the rounding of
`D = ⌈n^κ⌉` costs at most a factor two. Source: `08-scanner.tex`, lines 32–58. -/
theorem mul_ceil_rpow_le_floor_rpow {n c : ℕ} {kappa mu : ℝ} (hn : 1 ≤ n) (hkappa : 0 ≤ kappa)
    (hratio : 2 * (c : ℝ) ≤ (n : ℝ) ^ (mu - kappa)) :
    c * ⌈(n : ℝ) ^ kappa⌉₊ ≤ ⌊(n : ℝ) ^ mu⌋₊ := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ kappa := Real.one_le_rpow hnR hkappa
  have hceil : (⌈(n : ℝ) ^ kappa⌉₊ : ℝ) ≤ (n : ℝ) ^ kappa + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)).le
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  apply Nat.le_floor
  push_cast
  rw [show mu = kappa + (mu - kappa) by ring, Real.rpow_add (zero_lt_one.trans_le hnR)]
  nlinarith [mul_le_mul_of_nonneg_left hratio (zero_le_one.trans hpow),
    mul_le_mul_of_nonneg_left hceil hc, mul_le_mul_of_nonneg_left hpow hc]

/-- The explicit threshold of the status scale separation: `⌈Cr log² n⌉ ≤ n^κ` (which
already forces `n ≥ 3`) and `n^{μ-κ} ≥ 8` (`08-scanner.tex`, lines 32–58). -/
noncomputable def statusScaleSeparationThreshold (Cr kappa mu : ℝ) : ℕ :=
  max (roundedLogRadiusThreshold Cr kappa 1 1) (Real.natRpowThreshold (mu - kappa) 8)

/-- The source's rounded powers give the three literal scale inequalities used
by the status geometry at every `n` from the explicit threshold
`statusScaleSeparationThreshold Cr kappa mu` on (`08-scanner.tex`, lines 32–58). -/
theorem status_scale_separation_of_threshold_le {Cr ell kappa mu : ℝ}
    (hCr : 0 ≤ Cr) (hkappa : 0 < kappa) (hkm : kappa < mu) {n : ℕ}
    (hthr : statusScaleSeparationThreshold Cr kappa mu ≤ n) :
    let L := ⌊(n : ℝ) ^ (1 - ell)⌋₊
    let m := ⌊(n : ℝ) ^ mu⌋₊
    let D := ⌈(n : ℝ) ^ kappa⌉₊
    let K := L / (8 * m)
    2 ≤ n ∧ roundedLogRadius Cr n ≤ D ∧ 1 ≤ D ∧
      4 * D ≤ m ∧ 8 * K * m ≤ L := by
  simp only [statusScaleSeparationThreshold, max_le_iff] at hthr
  obtain ⟨hr, hratio⟩ := hthr
  have hn : 2 ≤ n := le_trans (by simp [roundedLogRadiusThreshold]) hr
  replace hr := const_mul_roundedLogRadius_pow_le_rpow_of_threshold_le hCr hkappa 1 1 hr
  rw [one_mul, pow_one] at hr
  replace hratio := Real.le_natCast_rpow_of_natRpowThreshold_le (sub_pos.mpr hkm) hratio
  dsimp only
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ kappa :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) hkappa.le
  refine ⟨hn, ?_, ?_, ?_, eight_mul_bandCount_mul_le _ _⟩
  · exact_mod_cast hr.trans (Nat.le_ceil ((n : ℝ) ^ kappa))
  · exact_mod_cast hpow.trans (Nat.le_ceil ((n : ℝ) ^ kappa))
  · exact mul_ceil_rpow_le_floor_rpow (by omega) hkappa.le (by push_cast; linarith)

/-- The source's rounded powers give the three literal scale inequalities used
by the status geometry. The fixed exponent gap controls the threshold. -/
theorem eventually_status_scale_separation {Cr ell kappa mu : ℝ}
    (hCr : 0 ≤ Cr) (hkappa : 0 < kappa) (hkm : kappa < mu) :
    ∀ᶠ n : ℕ in atTop,
      let L := ⌊(n : ℝ) ^ (1 - ell)⌋₊
      let m := ⌊(n : ℝ) ^ mu⌋₊
      let D := ⌈(n : ℝ) ^ kappa⌉₊
      let K := L / (8 * m)
      2 ≤ n ∧ roundedLogRadius Cr n ≤ D ∧ 1 ≤ D ∧
        4 * D ≤ m ∧ 8 * K * m ≤ L :=
  eventually_atTop.2 ⟨_, fun _ => status_scale_separation_of_threshold_le hCr hkappa hkm⟩

/-- The explicit threshold `⌈max 1 (8 ^ (1 / (1 - ℓ - μ)))⌉₊` beyond which the rounded band
count is positive, from `n^{1-ℓ-μ} ≥ 8` (`08-scanner.tex`, lines 32–41). -/
noncomputable def sourceBandCountThreshold (ell mu : ℝ) : ℕ :=
  Real.natRpowThreshold (1 - ell - mu) 8

/-- The exact rounded band count is positive at every `n` from the explicit threshold
`sourceBandCountThreshold ell mu` on, for a positive window exponent strictly below the
collar exponent (`08-scanner.tex`, lines 32–41). No unrounded quotient is substituted for
the integer division. -/
theorem one_le_source_bandCount_of_threshold_le {ell mu : ℝ}
    (hmu : 0 < mu) (hmuL : mu < 1 - ell) {n : ℕ}
    (hthr : sourceBandCountThreshold ell mu ≤ n) :
    1 ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * ⌊(n : ℝ) ^ mu⌋₊) := by
  have hn : 1 ≤ n := (Real.one_le_natRpowThreshold _ _).trans hthr
  have hratio := Real.le_natCast_rpow_of_natRpowThreshold_le (sub_pos.mpr hmuL) hthr
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hm : 1 ≤ ⌊(n : ℝ) ^ mu⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using Real.one_le_rpow hnR hmu.le)
  have hband : 8 * ⌊(n : ℝ) ^ mu⌋₊ ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ := by
    apply Nat.le_floor
    push_cast
    calc
      _ ≤ 8 * (n : ℝ) ^ mu :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
          (by norm_num)
      _ ≤ (n : ℝ) ^ mu * (n : ℝ) ^ (1 - ell - mu) := by
        nlinarith [mul_le_mul_of_nonneg_left hratio
          (Real.rpow_nonneg (Nat.cast_nonneg n) mu)]
      _ = (n : ℝ) ^ (1 - ell) := by rw [← Real.rpow_add hnpos, add_sub_cancel]
  exact Nat.div_pos hband (by omega)

/-- The exact rounded band count is positive eventually for each fixed positive
window exponent strictly below the collar exponent. No unrounded quotient is
substituted for the integer division. -/
theorem eventually_one_le_source_bandCount {ell mu : ℝ}
    (hmu : 0 < mu) (hmuL : mu < 1 - ell) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * ⌊(n : ℝ) ^ mu⌋₊) :=
  eventually_atTop.2 ⟨_, fun _ => one_le_source_bandCount_of_threshold_le hmu hmuL⟩

end TNLean.PEPS.AreaLaw.Scan
