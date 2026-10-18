/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Budgets
import TNLean.PEPS.AreaLaw.Geometry.Exponents
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rounded scanner weights in the marginal-moment interval

The literal floor and ceiling scales give a quantitative lower bound for the
band count. If the growth exponent of the total weight, plus half the marginal
budget exponent, is strictly below the band-count exponent, every fixed
multiple of the per-band weight eventually belongs to the marginal-moment
interval. The threshold is uniform over all weights and budgets satisfying
their stated bounds.

The strict exponent inequality is an explicit hypothesis of the general
numerical statement. It follows from the final collar parameters, but not
from the ordinary scanner exponent conditions alone. The thresholds are given explicitly
by `ScannerExponents.scaleFactsThreshold` and `ScannerExponents.momentRadiusThreshold`.
No marginal estimate,
physical state, comparator or bootstrap entropy improvement is constructed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:scales`, lines 32–41, and the final parameter
choice and marginal-moment smallness, lines 839–865, at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof is reused.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- The rounded band count retains its positive power growth with the coefficient `32` at
every `n` from the explicit threshold `X.scaleFactsThreshold` on. Source: `scanner:scales`,
`08-scanner.tex`, lines 32–41. -/
theorem ScannerExponents.rpow_le_mul_K_of_scaleFactsThreshold_le (X : ScannerExponents)
    {n : ℕ} (hthr : X.scaleFactsThreshold ≤ n) :
    2 ≤ n ∧ 1 ≤ X.K n ∧ (n : ℝ) ^ (1 - X.ell - X.mu) ≤ 32 * (X.K n : ℝ) := by
  have hn := scaleFacts_of_scaleFactsThreshold_le X hthr
  generalize hCdef : (32 : ℝ) = C at hn ⊢
  have hC1 : 1 ≤ C := hCdef ▸ by norm_num
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by have := hn.two_le_n; omega)
  have hmpos : (0 : ℝ) < X.m n := by
    exact_mod_cast (show 0 < X.m n by have := hn.one_le_m; omega)
  have hKpos : (0 : ℝ) < X.K n := by
    exact_mod_cast (show 0 < X.K n by have := hn.one_le_K; omega)
  have hDpos : (0 : ℝ) < X.D n := by
    exact_mod_cast (show 0 < X.D n by have := hn.one_le_D; omega)
  have hcoeff := (div_le_iff₀ (mul_pos hmpos hKpos)).mp hn.coefficient_le
  have hnle : (n : ℝ) ≤ C * (n : ℝ) ^ X.ell *
      ((X.m n : ℝ) * (X.K n : ℝ)) := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hDpos)).mp
    calc
      (n : ℝ) * (X.D n : ℝ) ^ 2
          ≤ C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 *
            ((X.m n : ℝ) * (X.K n : ℝ)) := hcoeff
      _ = (C * (n : ℝ) ^ X.ell *
          ((X.m n : ℝ) * (X.K n : ℝ))) * (X.D n : ℝ) ^ 2 := by ring
  have hmle : (X.m n : ℝ) ≤ (n : ℝ) ^ X.mu := Nat.floor_le (by positivity)
  have hpower : (n : ℝ) ≤ (C * (X.K n : ℝ)) *
      (n : ℝ) ^ (X.ell + X.mu) := by
    calc
      (n : ℝ) ≤ C * (n : ℝ) ^ X.ell *
          ((X.m n : ℝ) * (X.K n : ℝ)) := hnle
      _ ≤ C * (n : ℝ) ^ X.ell *
          ((n : ℝ) ^ X.mu * (X.K n : ℝ)) := by
        gcongr
      _ = (C * (X.K n : ℝ)) * (n : ℝ) ^ (X.ell + X.mu) := by
        rw [Real.rpow_add hnpos]
        ring
  refine ⟨hn.two_le_n, hn.one_le_K, ?_⟩
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hnpos (X.ell + X.mu))).mp
  calc
    (n : ℝ) ^ (1 - X.ell - X.mu) * (n : ℝ) ^ (X.ell + X.mu)
        = n := by
          rw [← Real.rpow_add hnpos,
            show 1 - X.ell - X.mu + (X.ell + X.mu) = (1 : ℝ) by ring,
            Real.rpow_one]
    _ ≤ (C * (X.K n : ℝ)) * (n : ℝ) ^ (X.ell + X.mu) := hpower

/-- The rounded band count retains its positive power growth with a fixed
coefficient. Source: `scanner:scales`, `08-scanner.tex`, lines 32–41. -/
theorem ScannerExponents.exists_eventually_rpow_le_mul_K (X : ScannerExponents) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ X.K n ∧
        (n : ℝ) ^ (1 - X.ell - X.mu) ≤ C * (X.K n : ℝ) :=
  ⟨32, by norm_num, eventually_atTop.2 ⟨_, fun _ => X.rpow_le_mul_K_of_scaleFactsThreshold_le⟩⟩

/-- A ceiling budget of order `n D (log n)^12` has the expected square-root
power bound, with the ceiling factor retained. Auxiliary to the smallness
estimate in `08-scanner.tex`, lines 859–865. -/
theorem ScannerExponents.sqrt_budget_le (X : ScannerExponents) {n : ℕ}
    (hn : 1 ≤ n) {CB B : ℝ} (hCB : 0 ≤ CB)
    (hB : B ≤ CB * (n : ℝ) * (X.D n : ℝ) * Real.log (n : ℝ) ^ 12) :
    Real.sqrt B ≤ Real.sqrt (2 * CB) *
      (n : ℝ) ^ ((1 + X.kappa) / 2) * Real.log (n : ℝ) ^ 6 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hκ : (1 : ℝ) ≤ (n : ℝ) ^ X.kappa :=
    Real.one_le_rpow hn1 X.kappa_pos.le
  have hD : (X.D n : ℝ) ≤ 2 * (n : ℝ) ^ X.kappa := by
    have hceil : (X.D n : ℝ) < (n : ℝ) ^ X.kappa + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have hB' : B ≤ (2 * CB) * (n : ℝ) ^ (1 + X.kappa) *
      Real.log (n : ℝ) ^ 12 := by
    calc
      B ≤ CB * (n : ℝ) * (X.D n : ℝ) * Real.log (n : ℝ) ^ 12 := hB
      _ ≤ CB * (n : ℝ) * (2 * (n : ℝ) ^ X.kappa) *
          Real.log (n : ℝ) ^ 12 := by gcongr
      _ = _ := by rw [Real.rpow_add hnpos, Real.rpow_one]; ring
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hpow : ((n : ℝ) ^ ((1 + X.kappa) / 2)) ^ 2 =
      (n : ℝ) ^ (1 + X.kappa) := by
    rw [← Real.rpow_mul_natCast hnpos.le]
    congr 1
    norm_num
  calc
    B ≤ (2 * CB) * (n : ℝ) ^ (1 + X.kappa) * Real.log (n : ℝ) ^ 12 := hB'
    _ = (Real.sqrt (2 * CB) * (n : ℝ) ^ ((1 + X.kappa) / 2) *
        Real.log (n : ℝ) ^ 6) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hpow]
      ring

/-- The explicit threshold of the sharp-comparison smallness bound: the scale-facts threshold
and the threshold for `32 A √(2 C_B) (log n)^6 ≤ c n^δ`, where
`δ = 1 - ℓ - μ - (ω + (1 + κ) / 2)` (`08-scanner.tex`, lines 859–865). -/
noncomputable def ScannerExponents.momentRadiusThreshold (X : ScannerExponents)
    (ω CB A c : ℝ) : ℕ :=
  max X.scaleFactsThreshold ⌈Real.logPowThreshold (A * 32 * Real.sqrt (2 * CB)) c
    (1 - X.ell - X.mu - (ω + (1 + X.kappa) / 2)) 6⌉₊

/-- The moment-radius threshold is at least `2`. -/
theorem ScannerExponents.two_le_momentRadiusThreshold (X : ScannerExponents) (ω CB A c : ℝ) :
    2 ≤ X.momentRadiusThreshold ω CB A c :=
  (le_max_left _ _).trans (le_max_left _ _)

/-- Under the explicit positive exponent margin, all admissible growing weights and marginal
budgets obey the sharp-comparison smallness bound at every `n` from the explicit threshold
`X.momentRadiusThreshold ω CB A c` on. Source: the numerical implication in
`08-scanner.tex`, lines 859–865. -/
theorem ScannerExponents.mul_a_sqrt_budget_le_of_momentRadiusThreshold_le
    (X : ScannerExponents) {ω CB A c : ℝ} (hmargin : ω + (1 + X.kappa) / 2 < 1 - X.ell - X.mu)
    (hCB : 0 ≤ CB) (hA : 0 ≤ A) (hc : 0 < c) {n : ℕ}
    (hthr : X.momentRadiusThreshold ω CB A c ≤ n) :
    2 ≤ n ∧ 1 ≤ X.K n ∧
      ∀ W B : ℝ, 0 ≤ W → W ≤ (n : ℝ) ^ ω →
        B ≤ CB * (n : ℝ) * (X.D n : ℝ) * Real.log (n : ℝ) ^ 12 →
        A * X.a W n * Real.sqrt B ≤ c := by
  have hn := X.rpow_le_mul_K_of_scaleFactsThreshold_le ((le_max_left _ _).trans hthr)
  let δ := 1 - X.ell - X.mu - (ω + (1 + X.kappa) / 2)
  have hδ : 0 < δ := sub_pos.mpr hmargin
  have hsmall' : A * 32 * Real.sqrt (2 * CB) * Real.log (n : ℝ) ^ 6 ≤ c * (n : ℝ) ^ δ :=
    Real.mul_log_pow_le_mul_rpow_of_ceil_logPowThreshold_le (by positivity) hc hδ
      ((le_max_right _ _).trans hthr)
  generalize hCdef : (32 : ℝ) = C at hn hsmall'
  have hC : (1 : ℝ) ≤ C := hCdef ▸ by norm_num
  refine ⟨hn.1, hn.2.1, ?_⟩
  intro W B hW hWle hB
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hKpos : (0 : ℝ) < X.K n := by
    exact_mod_cast (show 0 < X.K n by omega)
  have hroot := X.sqrt_budget_le hn1 hCB hB
  have hweight : A * W * Real.sqrt B ≤ c * (X.K n : ℝ) := by
    calc
      A * W * Real.sqrt B
          ≤ A * (n : ℝ) ^ ω *
            (Real.sqrt (2 * CB) * (n : ℝ) ^ ((1 + X.kappa) / 2) *
              Real.log (n : ℝ) ^ 6) := by gcongr
      _ = (A * Real.sqrt (2 * CB) * Real.log (n : ℝ) ^ 6) *
          (n : ℝ) ^ (ω + (1 + X.kappa) / 2) := by
        rw [Real.rpow_add hnpos]
        ring
      _ ≤ (c / C) * (n : ℝ) ^ δ *
          (n : ℝ) ^ (ω + (1 + X.kappa) / 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          A * Real.sqrt (2 * CB) * Real.log (n : ℝ) ^ 6
              ≤ (c * (n : ℝ) ^ δ) / C := by
                apply (le_div_iff₀ (zero_lt_one.trans_le hC)).2
                calc A * Real.sqrt (2 * CB) * Real.log (n : ℝ) ^ 6 * C
                    = A * C * Real.sqrt (2 * CB) * Real.log (n : ℝ) ^ 6 := by
                      ring
                  _ ≤ c * (n : ℝ) ^ δ := hsmall'
          _ = (c / C) * (n : ℝ) ^ δ := by ring
      _ = (c / C) * (n : ℝ) ^ (1 - X.ell - X.mu) := by
        rw [mul_assoc, ← Real.rpow_add hnpos]
        congr 2
        dsimp [δ]
        ring
      _ ≤ (c / C) * (C * (X.K n : ℝ)) :=
        mul_le_mul_of_nonneg_left hn.2.2 (by positivity)
      _ = c * (X.K n : ℝ) := by
        field_simp [(zero_lt_one.trans_le hC).ne']
  unfold ScannerExponents.a
  calc
    A * (W / (X.K n : ℝ)) * Real.sqrt B =
        (A * W * Real.sqrt B) / (X.K n : ℝ) := by ring
    _ ≤ c := (div_le_iff₀ hKpos).2 hweight

/-- Under the explicit positive exponent margin, all admissible growing
weights and marginal budgets obey one eventual sharp-comparison smallness
bound. The threshold precedes the scale, weight and budget.
Source: the numerical implication in `08-scanner.tex`, lines 859–865.
The ordinary scanner exponent hypotheses alone do not imply the margin. -/
theorem ScannerExponents.eventually_mul_a_sqrt_budget_le (X : ScannerExponents)
    {ω CB A c : ℝ} (hmargin : ω + (1 + X.kappa) / 2 < 1 - X.ell - X.mu)
    (hCB : 0 ≤ CB) (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ X.K n ∧
      ∀ W B : ℝ, 0 ≤ W → W ≤ (n : ℝ) ^ ω →
        B ≤ CB * (n : ℝ) * (X.D n : ℝ) * Real.log (n : ℝ) ^ 12 →
        A * X.a W n * Real.sqrt B ≤ c :=
  eventually_atTop.2
    ⟨_, fun _ => X.mul_a_sqrt_budget_le_of_momentRadiusThreshold_le hmargin hCB hA hc⟩

/-- Every fixed multiple of the per-band weight lies in the moment interval at every `n` from
the explicit threshold `X.momentRadiusThreshold ω CB A c` on, uniformly in positive admissible
budgets. Source: `07-comparators.tex`, lines 70–85 and 171–173, and `08-scanner.tex`,
lines 859–865. -/
theorem ScannerExponents.a_le_moment_radius_of_momentRadiusThreshold_le (X : ScannerExponents)
    {ω CB A c : ℝ} (hmargin : ω + (1 + X.kappa) / 2 < 1 - X.ell - X.mu)
    (hCB : 0 ≤ CB) (hA : 0 ≤ A) (hc : 0 < c) {n : ℕ}
    (hthr : X.momentRadiusThreshold ω CB A c ≤ n) :
    1 ≤ X.K n ∧
      ∀ W B : ℝ, 0 ≤ W → W ≤ (n : ℝ) ^ ω → 1 ≤ B →
        B ≤ CB * (n : ℝ) * (X.D n : ℝ) * Real.log (n : ℝ) ^ 12 →
        A * X.a W n ≤ c / Real.sqrt B := by
  obtain ⟨_, hK, hsmall⟩ :=
    X.mul_a_sqrt_budget_le_of_momentRadiusThreshold_le hmargin hCB hA hc hthr
  refine ⟨hK, ?_⟩
  intro W B hW hWle hB hBupper
  exact (le_div_iff₀ (Real.sqrt_pos.2 (zero_lt_one.trans_le hB))).2
    (hsmall W B hW hWle hBupper)

/-- Every fixed multiple of the per-band weight is eventually in the moment
interval, uniformly in positive admissible budgets. Source:
`07-comparators.tex`, lines 70–85 and 171–173, and
`08-scanner.tex`, lines 859–865. -/
theorem ScannerExponents.exists_a_le_moment_radius (X : ScannerExponents)
    {ω CB A c : ℝ} (hmargin : ω + (1 + X.kappa) / 2 < 1 - X.ell - X.mu)
    (hCB : 0 ≤ CB) (hA : 0 ≤ A) (hc : 0 < c) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ X.K n ∧
      ∀ W B : ℝ, 0 ≤ W → W ≤ (n : ℝ) ^ ω → 1 ≤ B →
        B ≤ CB * (n : ℝ) * (X.D n : ℝ) * Real.log (n : ℝ) ^ 12 →
        A * X.a W n ≤ c / Real.sqrt B :=
  ⟨_, X.two_le_momentRadiusThreshold ω CB A c,
    fun _ => X.a_le_moment_radius_of_momentRadiusThreshold_le hmargin hCB hA hc⟩

/-- The exact final scanner parameters have the positive margin used in the
sharp marginal-moment estimate. Source: `scanner:final-parameters` and
`08-scanner.tex`, lines 839–865. -/
theorem final_scanner_moment_margin :
    (1 - (Exponents.scannerEll : ℝ) - (Exponents.scannerMu : ℝ)) -
        ((Exponents.scannerOmega : ℝ) + (1 + (Exponents.scannerKappa : ℝ)) / 2) =
      (499879 / 2000000 : ℝ) := by
  norm_num [Exponents.scannerEll, Exponents.scannerMu,
    Exponents.scannerOmega, Exponents.scannerKappa]

/-- At the final collar parameters, every fixed real multiple of the actual
per-band weight lies in the common marginal-moment interval. Both floors,
the natural-number division and the separation ceiling are retained.
Source: `scanner:final-parameters` and `08-scanner.tex`, lines 839–865. -/
theorem exists_final_a_le_moment_radius {CB c : ℝ} (hCB : 0 ≤ CB)
    (hc : 0 < c) (t : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
      let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
      let K := L / (8 * m)
      let D := Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ))
      let a := (n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (K : ℝ)
      1 ≤ K ∧ ∀ B : ℝ, 1 ≤ B →
        B ≤ CB * (n : ℝ) * (D : ℝ) * Real.log (n : ℝ) ^ 12 →
        |t * a| ≤ c / Real.sqrt B := by
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
  have hmargin : (Exponents.scannerOmega : ℝ) + (1 + X.kappa) / 2 <
      1 - X.ell - X.mu := by
    have hgap := final_scanner_moment_margin
    change (Exponents.scannerOmega : ℝ) +
      (1 + (Exponents.scannerKappa : ℝ)) / 2 <
        1 - (Exponents.scannerEll : ℝ) - (Exponents.scannerMu : ℝ)
    linarith
  obtain ⟨N, hN, hbound⟩ := X.exists_a_le_moment_radius hmargin hCB (abs_nonneg t) hc
  refine ⟨N, hN, ?_⟩
  intro n hn
  change 1 ≤ X.K n ∧ ∀ B : ℝ, 1 ≤ B →
    B ≤ CB * (n : ℝ) * (X.D n : ℝ) * Real.log (n : ℝ) ^ 12 →
    |t * X.a ((n : ℝ) ^ (Exponents.scannerOmega : ℝ)) n| ≤ c / Real.sqrt B
  obtain ⟨hK, hsmall⟩ := hbound n hn
  refine ⟨hK, ?_⟩
  intro B hB hBupper
  have ha : 0 ≤ X.a ((n : ℝ) ^ (Exponents.scannerOmega : ℝ)) n := by
    unfold ScannerExponents.a
    positivity
  simpa only [abs_mul, abs_of_nonneg ha] using
    hsmall ((n : ℝ) ^ (Exponents.scannerOmega : ℝ)) B (by positivity) le_rfl hB hBupper

end TNLean.PEPS.AreaLaw.Scan
