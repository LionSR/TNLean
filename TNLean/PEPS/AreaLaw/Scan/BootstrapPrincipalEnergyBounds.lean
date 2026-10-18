/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapScannerExponents
import TNLean.PEPS.AreaLaw.Scan.Budgets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The numerical energy expression at the fixed bootstrap scales

Fix the initial exponent and all scalar and logarithmic coefficients before
the system size. The total metric weight is four. The threshold is uniform
in the current entropy exponent below the initial exponent. The collar and
window retain their floors, the number of bands retains its natural-number
division, and the separation retains its ceiling.

The principal term of the scanner energy estimate is bounded at the fixed
scales below. The fixed contribution \(C n^{-1000}\) is then included in the
energy bound with coefficient \(1+C\), at the same threshold. The separate
remainder tends to zero with the replica count. No physical energy estimate
is assumed, and no scan or entropy improvement is constructed. The threshold is given
explicitly by `bootstrapPrincipalEnergyThreshold`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:density-output`, lines 379–384;
`scanner:energy-output`, lines 371–377; `scanner:bootstrap-parameters`,
lines 693–703; and `scanner:bootstrap-energy`, lines 731–755, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit threshold of the bootstrap principal energy bound: the scale-facts threshold
of the bootstrap scanner exponents, `n^ν ≥ max 128 (2 C_δ)`, `(log n)^{C_{lδ}} ≤ n^ν` and
`192 C (log n)^{C_l} ≤ n^{ν/4}`, where `ν = ν(e₀)` (`08-scanner.tex`, lines 693–703 and
731–755). -/
noncomputable def bootstrapPrincipalEnergyThreshold {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (C Cδ Cl Clδ : ℝ) : ℕ :=
  max (BootstrapParameters.scannerExponents e₀ he₀ he₀₁).scaleFactsThreshold
    (max (Real.natRpowThreshold (BootstrapParameters.nu e₀) (max (4 * 32) (2 * Cδ)))
      (max ⌈Real.logRpowThreshold 1 1 0 (BootstrapParameters.nu e₀) Clδ⌉₊
        ⌈Real.logRpowThreshold (192 * C) 1 0 (BootstrapParameters.nu e₀ / 4) Cl⌉₊))

/-- With total metric weight four, the rounded principal energy expression is below the
bootstrap energy scale at every `n` from the explicit threshold
`bootstrapPrincipalEnergyThreshold he₀ he₀₁ C Cδ Cl Clδ` on, uniformly in every current
exponent `e ≤ e₀`. This is a numerical auxiliary to `08-scanner.tex`, lines 731–755. -/
theorem bootstrap_principal_energy_bound_of_threshold_le
    {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (C Cδ Cl Clδ : ℝ) (hC : 0 ≤ C) (hCδ : 0 ≤ Cδ) {n : ℕ}
    (hthr : bootstrapPrincipalEnergyThreshold he₀ he₀₁ C Cδ Cl Clδ ≤ n) :
    ∀ e : ℝ, e ≤ e₀ →
      let ℓ := BootstrapParameters.ell e₀
      let μ := BootstrapParameters.mu e₀
      let ν := BootstrapParameters.nu e₀
      let κ := BootstrapParameters.kappa e₀
      let L := Nat.floor ((n : ℝ) ^ (1 - ℓ))
      let m := Nat.floor ((n : ℝ) ^ μ)
      let K := L / (8 * m)
      let D := Nat.ceil ((n : ℝ) ^ κ)
      let a : ℝ := 4 / (K : ℝ)
      let δ := Cδ * ((n : ℝ) ^ (-ν))⁻¹ *
        ((n : ℝ) ^ (e - μ) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ)
      C * (n : ℝ) ^ ℓ * (D : ℝ) ^ 2 * (4 : ℝ) ^ 2 *
          Real.log (n : ℝ) ^ Cl *
          (δ ^ (1 / 8 : ℝ) + (n : ℝ) ^ (-ν) + (n : ℝ) ^ (-100 : ℝ)) ≤
        (n : ℝ) ^ (-ν / 2) := by
  obtain ⟨hg₀, hg₀half, hℓ, hℓ₁, hκ⟩ :=
    BootstrapParameters.parameter_bounds he₀ he₀₁
  have hℓg₀ : BootstrapParameters.ell e₀ < BootstrapParameters.g0 e₀ :=
    (div_lt_self (div_pos hg₀ (by norm_num : (0 : ℝ) < 1000))
      (by norm_num : (1 : ℝ) < 100)).trans
      (div_lt_self hg₀ (by norm_num : (1 : ℝ) < 1000))
  let X : ScannerExponents :=
    let hκμ : BootstrapParameters.kappa e₀ < BootstrapParameters.mu e₀ := by
      linarith [show BootstrapParameters.kappa e₀ ≤ BootstrapParameters.ell e₀ from
        min_le_left _ _, show BootstrapParameters.mu e₀ = 1 - BootstrapParameters.g0 e₀ from rfl]
    { ell := BootstrapParameters.ell e₀
      kappa := BootstrapParameters.kappa e₀
      mu := BootstrapParameters.mu e₀
      nu := BootstrapParameters.nu e₀
      e := BootstrapParameters.mu e₀
      ell_pos := hℓ
      ell_lt_one := hℓ₁
      kappa_pos := hκ
      kappa_lt_mu := hκμ
      mu_lt_one_sub_ell := sub_lt_sub_left hℓg₀ 1
      nu_pos := div_pos hg₀ (by norm_num)
      e_pos := hκ.trans hκμ
      e_lt_one := sub_lt_self 1 hg₀
      kappa_le_e := hκμ.le }
  simp only [bootstrapPrincipalEnergyThreshold, max_le_iff] at hthr
  obtain ⟨hsf, hνn, hlδ, hlC⟩ := hthr
  have hf : ScaleFacts X n 32 := scaleFacts_of_scaleFactsThreshold_le X hsf
  replace hνn := Real.le_natCast_rpow_of_natRpowThreshold_le X.nu_pos hνn
  have hC₁n : 4 * 32 ≤ (n : ℝ) ^ X.nu := (le_max_left _ _).trans hνn
  have hCδn : 2 * Cδ ≤ (n : ℝ) ^ X.nu := (le_max_right _ _).trans hνn
  have hlogδ : Real.log (n : ℝ) ^ Clδ ≤ (n : ℝ) ^ X.nu := by
    simpa only [Real.rpow_zero, mul_one, one_mul] using
      Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le zero_le_one one_pos
        X.nu_pos hlδ
  have hlogCn : 192 * C * Real.log (n : ℝ) ^ Cl ≤ (n : ℝ) ^ (X.nu / 4) := by
    simpa only [Real.rpow_zero, mul_one, one_mul] using
      Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le (by positivity) one_pos
        (div_pos X.nu_pos (by norm_num : (0 : ℝ) < 4)) hlC
  generalize (32 : ℝ) = C₁ at hf hC₁n
  intro e he
  obtain ⟨hn₁, hn₀, hm₀, hK₀, hD₀, hC₁, hlogn⟩ :
      (1 : ℝ) ≤ n ∧ 0 < (n : ℝ) ∧ 0 < (X.m n : ℝ) ∧
        0 < (X.K n : ℝ) ∧ 0 < (X.D n : ℝ) ∧ 0 ≤ C₁ ∧ 0 ≤ Real.log (n : ℝ) :=
    let hn₁ : (1 : ℝ) ≤ n := by
      exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) hf.two_le_n)
    ⟨hn₁, zero_lt_one.trans_le hn₁,
      Nat.cast_pos.mpr (zero_lt_one.trans_le hf.one_le_m),
      Nat.cast_pos.mpr (zero_lt_one.trans_le hf.one_le_K),
      Nat.cast_pos.mpr (zero_lt_one.trans_le hf.one_le_D),
      zero_le_one.trans hf.one_le_C₁, Real.log_nonneg hn₁⟩
  have hnCoeff : (n : ℝ) ≤
      C₁ * (n : ℝ) ^ X.ell * ((X.m n : ℝ) * (X.K n : ℝ)) :=
    (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hD₀)).mp (by
      convert (div_le_iff₀ (mul_pos hm₀ hK₀)).mp hf.coefficient_le using 1; ring)
  have hpowK : (n : ℝ) ^ (BootstrapParameters.g0 e₀ - X.ell) ≤ C₁ * (X.K n : ℝ) :=
    (mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos hn₀ (X.ell + X.mu))).mp <|
      calc
        (n : ℝ) ^ (BootstrapParameters.g0 e₀ - X.ell) * (n : ℝ) ^ (X.ell + X.mu) = n := by
          rw [← Real.rpow_add hn₀, show
            BootstrapParameters.g0 e₀ - X.ell + (X.ell + X.mu) = 1 by
              dsimp only [X, BootstrapParameters.mu]; ring, Real.rpow_one]
        _ ≤ C₁ * (n : ℝ) ^ X.ell * ((X.m n : ℝ) * (X.K n : ℝ)) := hnCoeff
        _ ≤ C₁ * (n : ℝ) ^ X.ell * ((n : ℝ) ^ X.mu * (X.K n : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (Nat.floor_le (Real.rpow_nonneg hn₀.le _)) hK₀.le)
            (mul_nonneg hC₁ (Real.rpow_nonneg hn₀.le _))
        _ = (C₁ * (X.K n : ℝ)) * (n : ℝ) ^ (X.ell + X.mu) := by
          rw [Real.rpow_add hn₀]; ring
  have ha : X.a 4 n ≤ (n : ℝ) ^ (-44 * X.nu) :=
    calc
      X.a 4 n ≤ (4 * C₁) / (n : ℝ) ^ (BootstrapParameters.g0 e₀ - X.ell) :=
        (div_le_div_iff₀ hK₀ (Real.rpow_pos_of_pos hn₀ _)).2 (by nlinarith [hpowK])
      _ = (4 * C₁) * (n : ℝ) ^ (-(BootstrapParameters.g0 e₀ - X.ell)) := by
        rw [div_eq_mul_inv, Real.rpow_neg hn₀.le]
      _ ≤ (n : ℝ) ^ X.nu * (n : ℝ) ^ (-(BootstrapParameters.g0 e₀ - X.ell)) :=
        mul_le_mul_of_nonneg_right hC₁n (Real.rpow_nonneg hn₀.le _)
      _ = (n : ℝ) ^ (X.nu - (BootstrapParameters.g0 e₀ - X.ell)) := by
        simpa only [sub_eq_add_neg] using
          (Real.rpow_add hn₀ X.nu (-(BootstrapParameters.g0 e₀ - X.ell))).symm
      _ ≤ (n : ℝ) ^ (-44 * X.nu) :=
        Real.rpow_le_rpow_of_exponent_le hn₁ (by
          dsimp only [X, BootstrapParameters.ell, BootstrapParameters.nu]
          linarith)
  have hsum : (n : ℝ) ^ (e - X.mu) +
      (X.a 4 n) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ ≤
        2 * (n : ℝ) ^ (-10 * X.nu) := by
    have hepow : (n : ℝ) ^ (e - X.mu) ≤ (n : ℝ) ^ (-10 * X.nu) :=
      Real.rpow_le_rpow_of_exponent_le hn₁ (by
        dsimp only [X, BootstrapParameters.mu, BootstrapParameters.nu, BootstrapParameters.g0]
        linarith)
    have haPow : (X.a 4 n) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (-11 * X.nu) :=
      (Real.rpow_le_rpow (div_nonneg (by norm_num) hK₀.le) ha
        (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans_eq (by
          rw [← Real.rpow_mul hn₀.le]
          congr 1; ring)
    calc
      (n : ℝ) ^ (e - X.mu) + (X.a 4 n) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ
          ≤ (n : ℝ) ^ (-10 * X.nu) + (n : ℝ) ^ (-11 * X.nu) * (n : ℝ) ^ X.nu :=
        add_le_add hepow (mul_le_mul haPow hlogδ
          (Real.rpow_nonneg hlogn _) (Real.rpow_nonneg hn₀.le _))
      _ = 2 * (n : ℝ) ^ (-10 * X.nu) := by
        rw [← Real.rpow_add hn₀, show -11 * X.nu + X.nu = -10 * X.nu by ring]
        ring
  let δ := Cδ * ((n : ℝ) ^ (-X.nu))⁻¹ *
    ((n : ℝ) ^ (e - X.mu) + (X.a 4 n) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ)
  obtain ⟨hδ₀, hδ⟩ : 0 ≤ δ ∧ δ ≤ (n : ℝ) ^ (-8 * X.nu) :=
    ⟨by dsimp only [δ, ScannerExponents.a]; positivity, by
      calc
        δ = Cδ * (n : ℝ) ^ X.nu *
            ((n : ℝ) ^ (e - X.mu) + (X.a 4 n) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ) := by
          dsimp only [δ]
          rw [Real.rpow_neg hn₀.le, inv_inv]
        _ ≤ Cδ * (n : ℝ) ^ X.nu * (2 * (n : ℝ) ^ (-10 * X.nu)) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hCδ (Real.rpow_nonneg hn₀.le _))
        _ = (2 * Cδ) * (n : ℝ) ^ (-9 * X.nu) := by
          rw [show -9 * X.nu = X.nu + (-10 * X.nu) by ring, Real.rpow_add hn₀]
          ring
        _ ≤ (n : ℝ) ^ X.nu * (n : ℝ) ^ (-9 * X.nu) :=
          mul_le_mul_of_nonneg_right hCδn (Real.rpow_nonneg hn₀.le _)
        _ = (n : ℝ) ^ (-8 * X.nu) := by
          rw [← Real.rpow_add hn₀]
          congr 1; ring⟩
  have hbracket : δ ^ (1 / 8 : ℝ) + (n : ℝ) ^ (-X.nu) + (n : ℝ) ^ (-100 : ℝ) ≤
      3 * (n : ℝ) ^ (-X.nu) := by
    have hroot : δ ^ (1 / 8 : ℝ) ≤ (n : ℝ) ^ (-X.nu) :=
      (Real.rpow_le_rpow hδ₀ hδ (by norm_num : (0 : ℝ) ≤ 1 / 8)).trans_eq (by
        rw [← Real.rpow_mul hn₀.le]
        congr 1; ring)
    have htail : (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-X.nu) :=
      Real.rpow_le_rpow_of_exponent_le hn₁ (by
        dsimp only [X, BootstrapParameters.nu]
        linarith)
    linarith
  have hDsq : (X.D n : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ (2 * X.kappa) := by
    have hceil : (X.D n : ℝ) ≤ 2 * (n : ℝ) ^ X.kappa :=
      (Nat.ceil_lt_add_one (Real.rpow_nonneg hn₀.le X.kappa)).le.trans
        (by linarith [Real.one_le_rpow hn₁ X.kappa_pos.le])
    calc
      (X.D n : ℝ) ^ 2 ≤ (2 * (n : ℝ) ^ X.kappa) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hceil 2
      _ = 4 * (n : ℝ) ^ (2 * X.kappa) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hn₀.le]
        norm_num [mul_comm]
  calc
    C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * (4 : ℝ) ^ 2 * Real.log (n : ℝ) ^ Cl *
        (δ ^ (1 / 8 : ℝ) + (n : ℝ) ^ (-X.nu) + (n : ℝ) ^ (-100 : ℝ))
        ≤ C * (n : ℝ) ^ X.ell * (4 * (n : ℝ) ^ (2 * X.kappa)) * (4 : ℝ) ^ 2 *
          Real.log (n : ℝ) ^ Cl * (3 * (n : ℝ) ^ (-X.nu)) := by
      gcongr
    _ = (192 * C * Real.log (n : ℝ) ^ Cl) *
        (n : ℝ) ^ (X.ell + 2 * X.kappa - X.nu) := by
      rw [Real.rpow_sub hn₀, Real.rpow_add hn₀, Real.rpow_neg hn₀.le, div_eq_mul_inv]
      ring
    _ ≤ (n : ℝ) ^ (X.nu / 4) * (n : ℝ) ^ (X.ell + 2 * X.kappa - X.nu) :=
      mul_le_mul_of_nonneg_right hlogCn (Real.rpow_nonneg hn₀.le _)
    _ = (n : ℝ) ^ (X.ell + 2 * X.kappa - 3 * X.nu / 4) := by
      rw [← Real.rpow_add hn₀]
      congr 1; ring
    _ ≤ (n : ℝ) ^ (-X.nu / 2) :=
      Real.rpow_le_rpow_of_exponent_le hn₁ (by
        have hk : X.kappa ≤ X.ell := min_le_left _ _
        dsimp only [X, BootstrapParameters.ell, BootstrapParameters.nu] at hk ⊢
        linarith)

/-- With total metric weight four, the rounded principal energy expression
is eventually below the bootstrap energy scale. Every coefficient is fixed
before the threshold, which precedes every current exponent `e ≤ e₀`.
The unit coefficient in the conclusion is obtained by increasing the threshold.
This is a numerical auxiliary to `08-scanner.tex`, lines 731–755;
no defect energy or entropy estimate is assumed. -/
theorem exists_bootstrap_principal_energy_bound
    {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (C Cδ Cl Clδ : ℝ) (hC : 0 ≤ C) (hCδ : 0 ≤ Cδ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ e : ℝ, e ≤ e₀ →
        let ℓ := BootstrapParameters.ell e₀
        let μ := BootstrapParameters.mu e₀
        let ν := BootstrapParameters.nu e₀
        let κ := BootstrapParameters.kappa e₀
        let L := Nat.floor ((n : ℝ) ^ (1 - ℓ))
        let m := Nat.floor ((n : ℝ) ^ μ)
        let K := L / (8 * m)
        let D := Nat.ceil ((n : ℝ) ^ κ)
        let a : ℝ := 4 / (K : ℝ)
        let δ := Cδ * ((n : ℝ) ^ (-ν))⁻¹ *
          ((n : ℝ) ^ (e - μ) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ)
        C * (n : ℝ) ^ ℓ * (D : ℝ) ^ 2 * (4 : ℝ) ^ 2 *
            Real.log (n : ℝ) ^ Cl *
            (δ ^ (1 / 8 : ℝ) + (n : ℝ) ^ (-ν) + (n : ℝ) ^ (-100 : ℝ)) ≤
          (n : ℝ) ^ (-ν / 2) :=
  ⟨_, (scaleFacts_of_scaleFactsThreshold_le _ (le_max_left _ _)).two_le_n,
    fun _ => bootstrap_principal_energy_bound_of_threshold_le he₀ he₀₁ C Cδ Cl Clδ hC hCδ⟩

/-- The principal and fixed numerical energy terms are eventually bounded
at the fixed bootstrap scales, uniformly in every current exponent `e ≤ e₀`.
The threshold is the one supplied by the principal-term bound. The fixed
term is retained in the scale-dependent energy budget.
Source: `08-scanner.tex`, `scanner:energy-output`, lines 371–377, and
`scanner:bootstrap-energy`, lines 744–755, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem exists_bootstrap_energy_expression_bound
    {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (C Cδ Cl Clδ : ℝ) (hC : 0 ≤ C) (hCδ : 0 ≤ Cδ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ e : ℝ, e ≤ e₀ →
        let ℓ := BootstrapParameters.ell e₀
        let μ := BootstrapParameters.mu e₀
        let ν := BootstrapParameters.nu e₀
        let κ := BootstrapParameters.kappa e₀
        let L := Nat.floor ((n : ℝ) ^ (1 - ℓ))
        let m := Nat.floor ((n : ℝ) ^ μ)
        let K := L / (8 * m)
        let D := Nat.ceil ((n : ℝ) ^ κ)
        let a : ℝ := 4 / (K : ℝ)
        let δ := Cδ * ((n : ℝ) ^ (-ν))⁻¹ *
          ((n : ℝ) ^ (e - μ) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ)
        let A := C * (n : ℝ) ^ ℓ * (D : ℝ) ^ 2 * (4 : ℝ) ^ 2 *
          Real.log (n : ℝ) ^ Cl *
          (δ ^ (1 / 8 : ℝ) + (n : ℝ) ^ (-ν) + (n : ℝ) ^ (-100 : ℝ))
        A + C * (n : ℝ) ^ (-1000 : ℝ) ≤ (1 + C) * (n : ℝ) ^ (-ν / 2) := by
  obtain ⟨N, hN, hprincipal⟩ :=
    exists_bootstrap_principal_energy_bound he₀ he₀₁ C Cδ Cl Clδ hC hCδ
  refine ⟨N, hN, fun n hn e he ↦ ?_⟩
  have hn₁ : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) (hN.trans hn))
  have hfixed : (n : ℝ) ^ (-1000 : ℝ) ≤
      (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn₁ (by
      dsimp only [BootstrapParameters.nu, BootstrapParameters.g0]
      linarith)
  calc
    _ ≤ (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2) +
        C * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2) :=
      add_le_add (hprincipal n hn e he) (mul_le_mul_of_nonneg_left hfixed hC)
    _ = (1 + C) * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2) := by ring

end TNLean.PEPS.AreaLaw.Scan
