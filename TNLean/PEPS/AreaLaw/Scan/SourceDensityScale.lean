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
are imposed. All constants and the threshold precede the scale and weight; the
threshold is given explicitly by `ScannerExponents.principalDensityThreshold`.
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

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit threshold of the principal density decay: the scale-facts threshold and the
thresholds for `32 C n^(e-μ) ≤ n^(-r-ν) / 2` and
`32^(1/4) C n^((ω-(1-ℓ-μ))/4) (log n)^Cl ≤ n^(-r-ν) / 2` (`scanner:density-output`,
`08-scanner.tex`, lines 380--384). -/
noncomputable def ScannerExponents.principalDensityThreshold (X : ScannerExponents)
    (C Cl ω r : ℝ) : ℕ :=
  max X.scaleFactsThreshold
    (max ⌈Real.logRpowThreshold (C * 32) (1 / 2) (X.e - X.mu) (-r - X.nu) 0⌉₊
      ⌈Real.logRpowThreshold (C * 32 ^ (1 / 4 : ℝ)) (1 / 2)
        ((ω - (1 - X.ell - X.mu)) / 4) (-r - X.nu) Cl⌉₊)

/-- The principal scanner density is at most `n^(-r)` at every `n` from the explicit
threshold `X.principalDensityThreshold C Cl ω r` on, uniformly in every admissible weight.
The floor in `m` and natural division in `K` are retained. Source:
`scanner:density-output`, `08-scanner.tex`, lines 380--384. -/
theorem ScannerExponents.principalDensity_le_rpow_of_principalDensityThreshold_le
    (X : ScannerExponents) {C Cl ω r : ℝ} (hC : 0 ≤ C)
    (hmargin_m : X.e - X.mu + X.nu < -r)
    (hmargin_a : (ω - (1 - X.ell - X.mu)) / 4 + X.nu < -r) {n : ℕ}
    (hthr : X.principalDensityThreshold C Cl ω r ≤ n) :
    2 ≤ n ∧ 1 ≤ X.K n ∧
      ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ ω →
        C * ((n : ℝ) ^ X.e / (X.m n : ℝ) +
          X.a W n ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) /
            (n : ℝ) ^ (-X.nu) ≤ (n : ℝ) ^ (-r) := by
  simp only [ScannerExponents.principalDensityThreshold, max_le_iff] at hthr
  obtain ⟨hscale, hfirst, hsecond⟩ := hthr
  have hn := scaleFacts_of_scaleFactsThreshold_le X hscale
  have hnK := X.rpow_le_mul_K_of_scaleFactsThreshold_le hscale
  have hm : (C * 32) * (n : ℝ) ^ (X.e - X.mu) ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (-r - X.nu) := by
    simpa only [Real.rpow_zero, mul_one] using
      Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le
        (by positivity) (by norm_num) (by linarith) hfirst
  have ha := Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le
    (by positivity) (by norm_num) (by linarith) hsecond
  generalize hCm : (32 : ℝ) = Cm at hn hm
  generalize hCK' : (32 : ℝ) = CK at hnK ha
  have hCK : 1 ≤ CK := hCK' ▸ by norm_num
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
            (n : ℝ) ^ (-X.nu) ≤ (n : ℝ) ^ (-r) :=
  eventually_atTop.2 ⟨_, fun _ =>
    X.principalDensity_le_rpow_of_principalDensityThreshold_le hC hmargin_m hmargin_a⟩

/-- Explicit threshold form of the uniform rounded-scale density bound. -/
theorem ScannerExponents.exists_principalDensity_le_rpow
    (X : ScannerExponents) {C Cl ω r : ℝ} (hC : 0 ≤ C)
    (hmargin_m : X.e - X.mu + X.nu < -r)
    (hmargin_a : (ω - (1 - X.ell - X.mu)) / 4 + X.nu < -r) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ X.K n ∧
      ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ ω →
        C * ((n : ℝ) ^ X.e / (X.m n : ℝ) +
          X.a W n ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) /
            (n : ℝ) ^ (-X.nu) ≤ (n : ℝ) ^ (-r) :=
  ⟨_, (le_max_left _ _).trans (le_max_left _ _), fun _ hn =>
    (X.principalDensity_le_rpow_of_principalDensityThreshold_le hC hmargin_m hmargin_a hn).2⟩

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

/-- The explicit threshold of the final principal-density bound at rate `r`: the
principal-density threshold of the final exponents at weight exponent `ω = 1/20000`
(`08-scanner.tex`, lines 380--384 and 839--865). -/
noncomputable def finalPrincipalDensityThreshold (C Cl r : ℝ) : ℕ :=
  finalSharpScannerExponents.principalDensityThreshold C Cl (Exponents.scannerOmega : ℝ) r

/-- The final principal-density threshold is at least `2`. -/
theorem two_le_finalPrincipalDensityThreshold (C Cl r : ℝ) :
    2 ≤ finalPrincipalDensityThreshold C Cl r :=
  (le_max_left _ _).trans (le_max_left _ _)

/-- At the final scanner exponents the principal density is at most `n^(-r)` at every `n`
from the explicit threshold `finalPrincipalDensityThreshold C Cl r` on, whenever `r` satisfies
both strict density margins. Source: `scanner:density-output`, `scanner:final-parameters`. -/
theorem final_principalDensity_le_rpow_of_finalPrincipalDensityThreshold_le {C Cl r : ℝ}
    (hC : 0 ≤ C)
    (hm : (Exponents.boxError : ℝ) - Exponents.scannerMu + Exponents.scannerNu < -r)
    (ha : ((Exponents.scannerOmega : ℝ) - (1 - Exponents.scannerEll - Exponents.scannerMu)) /
      4 + Exponents.scannerNu < -r) {n : ℕ} (hthr : finalPrincipalDensityThreshold C Cl r ≤ n) :
    let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
    let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
    let K := L / (8 * m)
    1 ≤ K ∧ ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
      C * ((n : ℝ) ^ (Exponents.boxError : ℝ) / (m : ℝ) +
        (W / (K : ℝ)) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) /
          (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) ≤ (n : ℝ) ^ (-r) :=
  (finalSharpScannerExponents.principalDensity_le_rpow_of_principalDensityThreshold_le
    hC hm ha hthr).2

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
              (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) :=
  ⟨_, two_le_finalPrincipalDensityThreshold C Cl _, fun _ =>
    final_principalDensity_le_rpow_of_finalPrincipalDensityThreshold_le hC
      (by norm_num [Exponents.boxError, Exponents.scannerMu, Exponents.scannerNu])
      (by norm_num [Exponents.scannerOmega, Exponents.scannerEll, Exponents.scannerMu,
        Exponents.scannerNu])⟩

end TNLean.PEPS.AreaLaw.Scan
