/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapPrincipalEnergyBounds

/-!
# Bootstrap energy at the same rough-selected interpolation

The scalar principal-energy bound is applied to the literal selected cap with
p in [epsilon, 2 epsilon]. It retains the physical gap normalization and the
truncated eigenvalue. The replica remainder is added only afterward. No energy
bound or entropy improvement is an input. The threshold is given explicitly by
`bootstrapPrincipalEnergyThreshold`.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 492--533 and
731--755, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The numerical cap at the selected interpolation has the bootstrap decay at every `n` from
the explicit threshold `bootstrapPrincipalEnergyThreshold he₀ he₀₁ (2 C / gap) Cδ Cl Clδ` on,
uniformly in the current exponent and the selected density and interpolation.
Source: `08-scanner.tex`, lines 731--755. -/
theorem bootstrap_selected_energy_bound_of_threshold_le
    {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (C Cδ Cl Clδ gap : ℝ) (hC : 0 ≤ C) (hCδ : 0 ≤ Cδ) (hgap : 0 < gap) {n : ℕ}
    (hthr : bootstrapPrincipalEnergyThreshold he₀ he₀₁ (2 * C / gap) Cδ Cl Clδ ≤ n) :
    ∀ e : ℝ, e ≤ e₀ →
      let ell := BootstrapParameters.ell e₀
      let mu := BootstrapParameters.mu e₀
      let nu := BootstrapParameters.nu e₀
      let kappa := BootstrapParameters.kappa e₀
      let L := Nat.floor ((n : ℝ) ^ (1 - ell))
      let m := Nat.floor ((n : ℝ) ^ mu)
      let K := L / (8 * m)
      let D := Nat.ceil ((n : ℝ) ^ kappa)
      let a := 4 / (K : ℝ)
      let epsilon := (n : ℝ) ^ (-nu)
      let delta := Cδ * epsilon⁻¹ *
        ((n : ℝ) ^ (e - mu) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ)
      ∀ rho p eigen : ℝ, 0 ≤ rho → rho ≤ delta →
        p ∈ Set.Icc epsilon (2 * epsilon) → p ≤ 1 →
        eigen ≤ (n : ℝ) ^ (-1000 : ℝ) →
        (eigen + C * (4 : ℝ) ^ 2 * (n : ℝ) ^ ell * (D : ℝ) ^ 2 *
          Real.log (n : ℝ) ^ Cl *
            ((1 - p) * rho ^ (1 / 8 : ℝ) + (1 - p) * (n : ℝ) ^ (-100 : ℝ) + p)) /
            gap ≤ (1 + gap⁻¹) * (n : ℝ) ^ (-nu / 2) := by
  have hprincipal := bootstrap_principal_energy_bound_of_threshold_le he₀ he₀₁
    (2 * C / gap) Cδ Cl Clδ (by positivity) hCδ hthr
  have hn2 := (scaleFacts_of_scaleFactsThreshold_le _ ((le_max_left _ _).trans hthr)).two_le_n
  intro e he ell mu nu kappa L m K D a epsilon delta rho p eigen
    hrho hdelta hp _hp1 heigen
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from (by omega))
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hepsilon : 0 < epsilon := Real.rpow_pos_of_pos hnpos _
  have hp0 : 0 ≤ p := hepsilon.le.trans hp.1
  have hroot0 : 0 ≤ rho ^ (1 / 8 : ℝ) := Real.rpow_nonneg hrho _
  have hroot : rho ^ (1 / 8 : ℝ) ≤ delta ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow hrho hdelta (by norm_num)
  have hdelta0 : 0 ≤ delta ^ (1 / 8 : ℝ) :=
    Real.rpow_nonneg (hrho.trans hdelta) _
  have htail : 0 ≤ (n : ℝ) ^ (-100 : ℝ) := Real.rpow_nonneg hnpos.le _
  have hbracket : (1 - p) * rho ^ (1 / 8 : ℝ) +
      (1 - p) * (n : ℝ) ^ (-100 : ℝ) + p ≤
        2 * (delta ^ (1 / 8 : ℝ) + epsilon + (n : ℝ) ^ (-100 : ℝ)) := by
    have h1 : (1 - p) * rho ^ (1 / 8 : ℝ) ≤ rho ^ (1 / 8 : ℝ) :=
      mul_le_of_le_one_left hroot0 (by linarith)
    have h2 : (1 - p) * (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-100 : ℝ) :=
      mul_le_of_le_one_left htail (by linarith)
    linarith [hp.2]
  let pref := (n : ℝ) ^ ell * (D : ℝ) ^ 2 * (4 : ℝ) ^ 2 * Real.log (n : ℝ) ^ Cl
  have hpref : 0 ≤ pref := by
    dsimp only [pref]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hn1) _)
  have hcap : (C * (4 : ℝ) ^ 2 * (n : ℝ) ^ ell * (D : ℝ) ^ 2 *
      Real.log (n : ℝ) ^ Cl *
        ((1 - p) * rho ^ (1 / 8 : ℝ) + (1 - p) * (n : ℝ) ^ (-100 : ℝ) + p)) /
          gap ≤ (n : ℝ) ^ (-nu / 2) := by
    calc
      _ = (C / gap) * pref *
          ((1 - p) * rho ^ (1 / 8 : ℝ) + (1 - p) * (n : ℝ) ^ (-100 : ℝ) + p) := by
        dsimp only [pref]; ring
      _ ≤ (C / gap) * pref *
          (2 * (delta ^ (1 / 8 : ℝ) + epsilon + (n : ℝ) ^ (-100 : ℝ))) :=
        mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ = (2 * C / gap) * (n : ℝ) ^ ell * (D : ℝ) ^ 2 * (4 : ℝ) ^ 2 *
          Real.log (n : ℝ) ^ Cl *
            (delta ^ (1 / 8 : ℝ) + epsilon + (n : ℝ) ^ (-100 : ℝ)) := by
        dsimp only [pref]; ring
      _ ≤ _ := hprincipal e he
  have hfixed : (n : ℝ) ^ (-1000 : ℝ) ≤ (n : ℝ) ^ (-nu / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by
      dsimp only [nu, BootstrapParameters.nu, BootstrapParameters.g0]
      linarith)
  have heigen' : eigen / gap ≤ gap⁻¹ * (n : ℝ) ^ (-nu / 2) := by
    calc
      eigen / gap ≤ (n : ℝ) ^ (-nu / 2) / gap :=
        div_le_div_of_nonneg_right (heigen.trans hfixed) hgap.le
      _ = _ := by ring
  rw [add_div]
  nlinarith only [heigen', hcap]

/-- The numerical cap at the selected interpolation has the bootstrap decay.
All coefficients and the initial exponent precede the threshold, which is
uniform in the current exponent and the selected density and interpolation.
Source: `08-scanner.tex`, lines 731--755. -/
theorem exists_bootstrap_selected_energy_bound
    {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (C Cδ Cl Clδ gap : ℝ) (hC : 0 ≤ C) (hCδ : 0 ≤ Cδ) (hgap : 0 < gap) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ e : ℝ, e ≤ e₀ →
      let ell := BootstrapParameters.ell e₀
      let mu := BootstrapParameters.mu e₀
      let nu := BootstrapParameters.nu e₀
      let kappa := BootstrapParameters.kappa e₀
      let L := Nat.floor ((n : ℝ) ^ (1 - ell))
      let m := Nat.floor ((n : ℝ) ^ mu)
      let K := L / (8 * m)
      let D := Nat.ceil ((n : ℝ) ^ kappa)
      let a := 4 / (K : ℝ)
      let epsilon := (n : ℝ) ^ (-nu)
      let delta := Cδ * epsilon⁻¹ *
        ((n : ℝ) ^ (e - mu) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ)
      ∀ rho p eigen : ℝ, 0 ≤ rho → rho ≤ delta →
        p ∈ Set.Icc epsilon (2 * epsilon) → p ≤ 1 →
        eigen ≤ (n : ℝ) ^ (-1000 : ℝ) →
        (eigen + C * (4 : ℝ) ^ 2 * (n : ℝ) ^ ell * (D : ℝ) ^ 2 *
          Real.log (n : ℝ) ^ Cl *
            ((1 - p) * rho ^ (1 / 8 : ℝ) + (1 - p) * (n : ℝ) ^ (-100 : ℝ) + p)) /
            gap ≤ (1 + gap⁻¹) * (n : ℝ) ^ (-nu / 2) :=
  ⟨_, (scaleFacts_of_scaleFactsThreshold_le _ (le_max_left _ _)).two_le_n,
    fun _ => bootstrap_selected_energy_bound_of_threshold_le he₀ he₀₁ C Cδ Cl Clδ gap hC hCδ hgap⟩

end TNLean.PEPS.AreaLaw.Scan
