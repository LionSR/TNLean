/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SelectedDensityPower

/-!
# The stronger density power on the unchanged source interval

The interval width remains `n^(-nu)`, while the selected density is bounded
by `n^(-8*nu)`. This uses the existing large strict margins; no physical
hypothesis or scale changes. The eighth root then has exponent `-nu`, matching
the source interval for the selected-energy estimate. All coefficients precede
the size threshold. Replica remainders are absorbed only afterward for each
fixed physical instance, without changing its selected point.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 457–490 and 839–911, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Filter
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- Exact density exponent margins at rate `8*nu`, with the interval
exponent still equal to `nu`. -/
theorem final_eightNuDensity_margins :
    -(8 * (Exponents.scannerNu : ℝ)) -
        ((Exponents.boxError : ℝ) - (Exponents.scannerMu : ℝ) +
          (Exponents.scannerNu : ℝ)) = (120499 / 500000 : ℝ) ∧
    -(8 * (Exponents.scannerNu : ℝ)) -
        (((Exponents.scannerOmega : ℝ) -
          (1 - (Exponents.scannerEll : ℝ) - (Exponents.scannerMu : ℝ))) / 4 +
            (Exponents.scannerNu : ℝ)) = (35697 / 200000 : ℝ) := by
  norm_num [Exponents.scannerNu, Exponents.boxError, Exponents.scannerMu,
    Exponents.scannerOmega, Exponents.scannerEll]

/-- At the final scanner exponents the principal density is at most
`n^(-8*nu)`, uniformly over the full weight interval. Both floors and the
natural-number division are literal, and the fixed constants precede `n`
and `W`. The charge-separation ceiling does not enter this numerical density.
Source: `scanner:scales`, `scanner:density-output`, `scanner:final-parameters`. -/
theorem exists_final_principalDensity_le_eightNu {C Cl : ℝ} (hC : 0 ≤ C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
      let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
      let K := L / (8 * m)
      1 ≤ K ∧ ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
        C * ((n : ℝ) ^ (Exponents.boxError : ℝ) / (m : ℝ) +
          (W / (K : ℝ)) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) /
            (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) ≤
              (n : ℝ) ^ (-(8 * (Exponents.scannerNu : ℝ))) := by
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
  have hm : X.e - X.mu + X.nu < -(8 * X.nu) := by
    norm_num [X, Exponents.boxError, Exponents.scannerMu, Exponents.scannerNu]
  have ha : ((Exponents.scannerOmega : ℝ) - (1 - X.ell - X.mu)) / 4 +
      X.nu < -(8 * X.nu) := by
    norm_num [X, Exponents.scannerOmega, Exponents.scannerEll,
      Exponents.scannerMu, Exponents.scannerNu]
  exact X.exists_principalDensity_le_rpow (Cl := Cl) hC hm ha


/-- The raw actual-selector density budget has the final source power while
preserving all propositions attached to its original selected point. The size
threshold precedes every physical scalar and replica remainder; the replica
threshold is chosen afterward for that fixed physical instance.
Source: `08-scanner.tex`, lines 457–490 and 839–865. -/
theorem exists_final_selectedDensity_le_eightNu
    {q : ℕ} (hq : 1 ≤ q) (Ce C₁ Ct Cl : ℝ)
    (hCe : 0 ≤ Ce) (hC : 0 < C₁) (hCt : 0 ≤ Ct) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
      let m := ⌊(n : ℝ) ^ (Exponents.scannerMu : ℝ)⌋₊
      let K := L / (8 * m)
      let D := ⌈(n : ℝ) ^ (Exponents.scannerKappa : ℝ)⌉₊
      let e := (Exponents.boxError : ℝ)
      ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
      let a := W / (K : ℝ)
      let ε := (n : ℝ) ^ (-(Exponents.scannerNu : ℝ))
      ∀ St logd z Bsh G : ℝ, 0 < z → 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z →
        St ≤ Ce * (n : ℝ) ^ (1 + e) + (n : ℝ) ^ (-247 : ℝ) →
        |logd - St| ≤ (n : ℝ) ^ (3 / 5 : ℝ) - Real.log z →
        Bsh ≤ Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ) →
        G ≤ Ct * Real.log (n : ℝ) ^ Cl →
        let Brough := 2 * logd - Real.log z + W *
          (Bsh / z + (1 + 3 * (n : ℝ) * D * Real.log q))
        ∀ R : ℕ → ℝ, Tendsto R atTop (𝓝 0) →
        ∀ {α : Type*} (density : ℕ → α → ℝ → ℝ) (keep : ℕ → α → ℝ → Prop)
          (p₀ p₁ : ℝ),
          (∀ᶠ k : ℕ in atTop, ∃ x : α, ∃ p ∈ Set.Icc p₀ p₁,
            density k x p ≤ (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)) *
              (Brough + ((2 * n * m : ℕ) : ℝ) * G * W * a ^ (1 / 4 : ℝ) + R k) ∧
                keep k x p) →
          ∀ᶠ k : ℕ in atTop, ∃ x : α, ∃ p ∈ Set.Icc p₀ p₁,
            density k x p ≤ (n : ℝ) ^ (-(8 * (Exponents.scannerNu : ℝ))) ∧
              keep k x p := by
  let Cr := 6 * Ce + 13 + 6 * Real.log q
  let C := 2 * (C₁ + 1) * (Cr + 2 * Ct)
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hCr : 0 ≤ Cr := by dsimp only [Cr]; positivity
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨N, hN, hprincipal⟩ :=
    exists_final_principalDensity_le_eightNu (C := 2 * C) (Cl := Cl) (by positivity)
  refine ⟨N, hN, ?_⟩
  intro n hn L m K D e W hW hWupper a ε St logd z Bsh G hz hmass
    hSt hlogd hBsh hG Brough R hR α density keep p₀ p₁ hselected
  obtain ⟨hK, hprincipalN⟩ := hprincipal n hn
  have hn2 : 2 ≤ n := hN.trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have hK0 : K = 0 := by simp only [K, hm0, Nat.mul_zero, Nat.div_zero]
    change 1 ≤ K at hK
    omega
  have hL : L ≤ n := by
    apply Nat.floor_le_of_le
    simpa using Real.rpow_le_rpow_of_exponent_le hn1
      (by norm_num [Exponents.scannerEll] :
        1 - (Exponents.scannerEll : ℝ) ≤ 1)
  have hD : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hκ1 : (1 : ℝ) ≤ (n : ℝ) ^ (Exponents.scannerKappa : ℝ) :=
    Real.one_le_rpow hn1 (by norm_num [Exponents.scannerKappa])
  have hDpower : (D : ℝ) ≤ 2 * (n : ℝ) ^ e := by
    have hceil : (D : ℝ) < (n : ℝ) ^ (Exponents.scannerKappa : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hκe : (n : ℝ) ^ (Exponents.scannerKappa : ℝ) ≤ (n : ℝ) ^ e :=
      Real.rpow_le_rpow_of_exponent_le hn1
        (by norm_num [e, Exponents.scannerKappa, Exponents.boxError])
    linarith
  have hWpos : 0 < W := zero_lt_one.trans_le hW
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hε : 0 < ε := Real.rpow_pos_of_pos hnpos _
  have hrough : Brough ≤ Cr * W * (n : ℝ) ^ (1 + e) :=
    roughBudget_le_source_power hn2 hq (by norm_num [e, Exponents.boxError])
      hCe hW hL hD hDpower hz hmass hSt hlogd hBsh
  let η := (n : ℝ) ^ (-(8 * (Exponents.scannerNu : ℝ)))
  have hη : 0 < η := Real.rpow_pos_of_pos hnpos _
  have hhalf : C * ((n : ℝ) ^ e / (m : ℝ) +
      a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε ≤ η / 2 := by
    have hdouble := hprincipalN W hW hWupper
    change 2 * C * ((n : ℝ) ^ e / (m : ℝ) +
      a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε ≤ η at hdouble
    have hdouble' : 2 * (C * ((n : ℝ) ^ e / (m : ℝ) +
        a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε) ≤ η := by
      convert hdouble using 1; ring
    linarith only [hdouble']
  let coeff := 2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)
  have hrem : Tendsto (fun k ↦ coeff * R k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hR.const_mul coeff
  have hremSmall : ∀ᶠ k : ℕ in atTop, coeff * R k ≤ η / 2 :=
    ((tendsto_order.mp hrem).2 (η / 2) (by positivity)).mono fun _ h ↦ h.le
  filter_upwards [hselected, hremSmall] with k hselectedK hremK
  obtain ⟨x, p, hp, hQ, hx⟩ := hselectedK
  refine ⟨x, p, hp, ?_, hx⟩
  have hbudget := selectedDensity_budget_le_principal
    (show 0 < n by omega) hm hWpos ha hε hC hCr hCt hrough hG
    (R := R k)
  have hbound : density k x p ≤
      C * ((n : ℝ) ^ e / (m : ℝ) +
        a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε + coeff * R k :=
    hQ.trans hbudget
  linarith

end TNLean.PEPS.AreaLaw.Scan
