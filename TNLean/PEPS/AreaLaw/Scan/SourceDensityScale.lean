/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SharpMomentScale

/-!
# Decay of the principal scanner density at the rounded scales

The literal scales `m = floor(n^mu)` and
`K = floor(n^(1-ell)) / (8 * m)` give the principal density bound

`C * (n^e / m + (W/K)^(1/4) * (log n)^Cl) / n^(-nu) <= n^(-r)`

uniformly over `1 <= W <= n^omega`, once the two strict exponent margins
are imposed. All constants and the threshold precede the scale and weight.
The final source parameters satisfy these margins with `r = nu`.

Only the numerical scale theorems are used. No physical state, entropy,
selected-point estimate, terminal bound or `ScanData` is a premise.
Applying this result to a selected entropy defect still requires the actual
comparison and endpoint arguments giving the displayed principal density.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:scales`, lines 32--41,
`scanner:density-output`, lines 380--384, and
`scanner:final-parameters`, lines 839--865, at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof is reused.
-/

open Filter Asymptotics

namespace TNLean.PEPS.AreaLaw.Scan

/-- A fixed logarithmic power and coefficient are absorbed by any strictly
positive power gap. The coefficient on the right can be arbitrarily small. -/
private theorem eventually_const_mul_rpow_log_rpow_le
    (A Cl p q b : ℝ) (hA : 0 ≤ A) (hpq : p < q) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      A * (n : ℝ) ^ p * Real.log (n : ℝ) ^ Cl ≤ b * (n : ℝ) ^ q := by
  have hgap : 0 < q - p := sub_pos.mpr hpq
  have hlog : (fun n : ℕ => A * Real.log (n : ℝ) ^ Cl) =o[atTop]
      fun n => (n : ℝ) ^ (q - p) :=
    (isLittleO_log_rpow_rpow_atTop Cl hgap).natCast_atTop.const_mul_left A
  filter_upwards [eventually_ge_atTop 2, hlog.bound hb] with n hn hsmall
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hsmall' : A * Real.log (n : ℝ) ^ Cl ≤ b * (n : ℝ) ^ (q - p) := by
    simpa only [Real.norm_of_nonneg
      (mul_nonneg hA (Real.rpow_nonneg hlog0 Cl)),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (q - p))]
      using hsmall
  calc
    A * (n : ℝ) ^ p * Real.log (n : ℝ) ^ Cl =
        (A * Real.log (n : ℝ) ^ Cl) * (n : ℝ) ^ p := by ring
    _ ≤ (b * (n : ℝ) ^ (q - p)) * (n : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right hsmall' (by positivity)
    _ = b * (n : ℝ) ^ q := by
      rw [mul_assoc, ← Real.rpow_add hnpos, sub_add_cancel]

/-- The principal scanner density decays at any rate allowed by both strict
exponent margins. The floor in `m` and natural division in `K` are retained.
The threshold is uniform in every admissible weight, and depends only on the
fixed exponents and constants. Source: `scanner:density-output`,
`08-scanner.tex`, lines 380--384. -/
theorem ScannerExponents.eventually_principalDensity_le_rpow
    (X : ScannerExponents) {C Cl ω r : ℝ} (hC : 0 ≤ C)
    (hmargin_m : X.e - X.mu + X.nu < -r)
    (hmargin_a : (ω - (1 - X.ell - X.mu)) / 4 + X.nu < -r) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ X.K n ∧
      ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ ω →
        C * ((n : ℝ) ^ X.e / (X.m n : ℝ) +
          X.a W n ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) /
            (n : ℝ) ^ (-X.nu) ≤ (n : ℝ) ^ (-r) := by
  obtain ⟨Cm, hscale⟩ := eventually_scaleFacts X
  have hCm : 1 ≤ Cm := (hscale.exists).choose_spec.one_le_C₁
  obtain ⟨CK, hCK, hK⟩ := X.exists_eventually_rpow_le_mul_K
  have hfirst : ∀ᶠ n : ℕ in atTop,
      (C * Cm) * (n : ℝ) ^ (X.e - X.mu) ≤
        (1 / 2 : ℝ) * (n : ℝ) ^ (-r - X.nu) := by
    simpa only [Real.rpow_zero, mul_one] using
      eventually_const_mul_rpow_log_rpow_le (C * Cm) 0
        (X.e - X.mu) (-r - X.nu) (1 / 2)
        (mul_nonneg hC (zero_le_one.trans hCm)) (by linarith) (by norm_num)
  have hsecond : ∀ᶠ n : ℕ in atTop,
      (C * CK ^ (1 / 4 : ℝ)) *
          (n : ℝ) ^ ((ω - (1 - X.ell - X.mu)) / 4) *
          Real.log (n : ℝ) ^ Cl ≤
        (1 / 2 : ℝ) * (n : ℝ) ^ (-r - X.nu) :=
    eventually_const_mul_rpow_log_rpow_le (C * CK ^ (1 / 4 : ℝ)) Cl
      ((ω - (1 - X.ell - X.mu)) / 4) (-r - X.nu) (1 / 2)
      (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hCK) _))
      (by linarith) (by norm_num)
  filter_upwards [hscale, hK, hfirst, hsecond] with n hn hnK hm ha
  refine ⟨hn.two_le_n, hn.one_le_K, ?_⟩
  intro W hW hWupper
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by have := hn.two_le_n; omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hKpos : (0 : ℝ) < X.K n := by
    exact_mod_cast (show 0 < X.K n by have := hn.one_le_K; omega)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlogpow0 : 0 ≤ Real.log (n : ℝ) ^ Cl := Real.rpow_nonneg hlog0 Cl
  have ha0 : 0 ≤ X.a W n := by
    unfold ScannerExponents.a
    exact div_nonneg (zero_le_one.trans hW) hKpos.le
  have ha_le : X.a W n ≤ CK * (n : ℝ) ^ (ω - (1 - X.ell - X.mu)) := by
    unfold ScannerExponents.a
    apply (div_le_iff₀ hKpos).2
    calc
      W ≤ (n : ℝ) ^ ω := hWupper
      _ = (n : ℝ) ^ (ω - (1 - X.ell - X.mu)) *
          (n : ℝ) ^ (1 - X.ell - X.mu) := by
        rw [← Real.rpow_add hnpos, sub_add_cancel]
      _ ≤ (n : ℝ) ^ (ω - (1 - X.ell - X.mu)) *
          (CK * (X.K n : ℝ)) :=
        mul_le_mul_of_nonneg_left hnK.2.2 (by positivity)
      _ = (CK * (n : ℝ) ^ (ω - (1 - X.ell - X.mu))) *
          (X.K n : ℝ) := by ring
  have ha_quarter : X.a W n ^ (1 / 4 : ℝ) ≤ CK ^ (1 / 4 : ℝ) *
      (n : ℝ) ^ ((ω - (1 - X.ell - X.mu)) / 4) := by
    calc
      X.a W n ^ (1 / 4 : ℝ) ≤
          (CK * (n : ℝ) ^ (ω - (1 - X.ell - X.mu))) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow ha0 ha_le (by norm_num)
      _ = CK ^ (1 / 4 : ℝ) *
          (n : ℝ) ^ ((ω - (1 - X.ell - X.mu)) / 4) := by
        rw [Real.mul_rpow (zero_le_one.trans hCK) (by positivity),
          ← Real.rpow_mul hnpos.le]
        congr 2
        ring
  have hnum : C * ((n : ℝ) ^ X.e / (X.m n : ℝ) +
      X.a W n ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) ≤
        (n : ℝ) ^ (-r - X.nu) := by
    calc
      C * ((n : ℝ) ^ X.e / (X.m n : ℝ) +
          X.a W n ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) ≤
          C * (Cm * (n : ℝ) ^ (X.e - X.mu) +
            (CK ^ (1 / 4 : ℝ) *
              (n : ℝ) ^ ((ω - (1 - X.ell - X.mu)) / 4)) *
                Real.log (n : ℝ) ^ Cl) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add hn.pow_e_div_m_le
            (mul_le_mul_of_nonneg_right ha_quarter hlogpow0)) hC
      _ = (C * Cm) * (n : ℝ) ^ (X.e - X.mu) +
          (C * CK ^ (1 / 4 : ℝ)) *
            (n : ℝ) ^ ((ω - (1 - X.ell - X.mu)) / 4) *
              Real.log (n : ℝ) ^ Cl := by ring
      _ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (-r - X.nu) +
          (1 / 2 : ℝ) * (n : ℝ) ^ (-r - X.nu) := add_le_add hm ha
      _ = (n : ℝ) ^ (-r - X.nu) := by ring
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hnpos (-X.nu))).2
  calc
    C * ((n : ℝ) ^ X.e / (X.m n : ℝ) +
        X.a W n ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) ≤
        (n : ℝ) ^ (-r - X.nu) := hnum
    _ = (n : ℝ) ^ (-r) * (n : ℝ) ^ (-X.nu) := by
      rw [← Real.rpow_add hnpos]
      congr 1

/-- Explicit threshold form of the uniform rounded-scale density bound. -/
theorem ScannerExponents.exists_principalDensity_le_rpow
    (X : ScannerExponents) {C Cl ω r : ℝ} (hC : 0 ≤ C)
    (hmargin_m : X.e - X.mu + X.nu < -r)
    (hmargin_a : (ω - (1 - X.ell - X.mu)) / 4 + X.nu < -r) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ X.K n ∧
      ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ ω →
        C * ((n : ℝ) ^ X.e / (X.m n : ℝ) +
          X.a W n ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) /
            (n : ℝ) ^ (-X.nu) ≤ (n : ℝ) ^ (-r) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (X.eventually_principalDensity_le_rpow (Cl := Cl) hC hmargin_m hmargin_a)
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn
  exact (hN n ((le_max_left N 2).trans hn)).2

/-- The two exact power gaps for decay at rate `nu` under the final source
parameters. They are independent of every coefficient and logarithmic power. -/
theorem final_principalDensity_margins :
    -(Exponents.scannerNu : ℝ) -
        ((Exponents.boxError : ℝ) - (Exponents.scannerMu : ℝ) +
          (Exponents.scannerNu : ℝ)) = (123999 / 500000 : ℝ) ∧
    -(Exponents.scannerNu : ℝ) -
        (((Exponents.scannerOmega : ℝ) -
          (1 - (Exponents.scannerEll : ℝ) - (Exponents.scannerMu : ℝ))) / 4 +
            (Exponents.scannerNu : ℝ)) = (37097 / 200000 : ℝ) := by
  norm_num [Exponents.scannerNu, Exponents.boxError, Exponents.scannerMu,
    Exponents.scannerOmega, Exponents.scannerEll]

/-- At the final scanner exponents the principal density is at most
`n^(-nu)`, uniformly over the full weight interval. Both floors and the
natural-number division are literal, and the fixed constants precede `n`
and `W`. The charge-separation ceiling does not enter this numerical density.
Source: `scanner:scales`, `scanner:density-output`, `scanner:final-parameters`. -/
theorem exists_final_principalDensity_le_rpow {C Cl : ℝ} (hC : 0 ≤ C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
      let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
      let K := L / (8 * m)
      1 ≤ K ∧ ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
        C * ((n : ℝ) ^ (Exponents.boxError : ℝ) / (m : ℝ) +
          (W / (K : ℝ)) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) /
            (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) ≤
              (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) := by
  let X : ScannerExponents :=
    { ell := Exponents.scannerEll
      kappa := Exponents.scannerKappa
      mu := Exponents.scannerMu
      nu := Exponents.scannerNu
      e := Exponents.boxError
      ell_pos := by norm_num [Exponents.scannerEll]
      ell_lt_one := by norm_num [Exponents.scannerEll]
      kappa_pos := by norm_num [Exponents.scannerKappa]
      kappa_lt_mu := by norm_num [Exponents.scannerKappa, Exponents.scannerMu]
      mu_lt_one_sub_ell := by norm_num [Exponents.scannerMu, Exponents.scannerEll]
      nu_pos := by norm_num [Exponents.scannerNu]
      e_pos := by norm_num [Exponents.boxError]
      e_lt_one := by norm_num [Exponents.boxError]
      kappa_le_e := by norm_num [Exponents.scannerKappa, Exponents.boxError] }
  have hm : X.e - X.mu + X.nu < -X.nu := by
    norm_num [X, Exponents.boxError, Exponents.scannerMu, Exponents.scannerNu]
  have ha : ((Exponents.scannerOmega : ℝ) - (1 - X.ell - X.mu)) / 4 +
      X.nu < -X.nu := by
    norm_num [X, Exponents.scannerOmega, Exponents.scannerEll,
      Exponents.scannerMu, Exponents.scannerNu]
  exact X.exists_principalDensity_le_rpow (Cl := Cl) hC hm ha

end TNLean.PEPS.AreaLaw.Scan
