/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Collar.Scales.Budgets
import QICLean.ManyBody.Entropy.MutualInformationPerturbation
import QICLean.ManyBody.Entropy.Typical.CompressedTypicalSiteCoordinates
import TNLean.PEPS.AreaLaw.Collar.Defs
import TNLean.PEPS.AreaLaw.Collar.Scales.SourceDensityScale

/-!
# The actual rough budget has the source entropy power

The displayed rough comparator budget is bounded from its physical target
entropy, selected spectral dimension, mass and shell entropy estimates.
No `ScanData` terminal bound or selected-density bound is used. The explicit
coefficient depends only on the fixed entropy coefficient and local dimension.
The ceiling separation cost is retained through its bound by twice `n^e`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 399–404 and 457–490, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## The selected-density budget on the source interpolation interval

The endpoint budget is converted to the
source density at arbitrary scanner exponents and positive total weight.
The interval is [ε/2, ε], and the replica remainder is retained exactly.
The endpoint and transport-coefficient estimates refer to the same state
and label sequence. The total weight has no prescribed upper growth bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 9.2, `08-scanner.tex`, lines 349–397 and 480–490, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Source-power decay at the unchanged selected point

The original target and shell entropy conclusions, target spectral window,
fixed logarithmic transport cap and literal final scales bound the raw selected
density. Its replica remainder is absorbed only after fixing the physical data.
An attached proposition retains the energy and sharp-comparison conclusions
already proved at the same selected point; it cannot change that point.

The coefficient and the entropy input precede the size threshold. No endpoint
estimate or density-power estimate is a premise. The raw selection inequality
is exactly the output to be supplied by the actual source scanner consumer.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 457–490 and 839–865, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- The same target-window and entropy-transfer conclusions bound the literal
rough expression. Here `logd` is the logarithm of the supplied target-set
cardinality, and `St` its physical regional entropy. The logarithmic-dimension
premise is the accepted selected-spectrum estimate for that same set.
Source: `08-scanner.tex`, lines 399–404 and 462–470. -/
theorem roughBudget_le_source_power
    {n L D q : ℕ} {e Ce W z logd St Bsh : ℝ}
    (hn : 2 ≤ n) (hq : 1 ≤ q) (he : 0 ≤ e) (hCe : 0 ≤ Ce)
    (hW : 1 ≤ W) (hL : L ≤ n) (hD : 1 ≤ D)
    (hDpower : (D : ℝ) ≤ 2 * (n : ℝ) ^ e)
    (hz : 0 < z) (hmass : 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z)
    (hSt : St ≤ Ce * (n : ℝ) ^ (1 + e) + (n : ℝ) ^ (-247 : ℝ))
    (hlogd : |logd - St| ≤ (n : ℝ) ^ (3 / 5 : ℝ) - Real.log z)
    (hBsh : Bsh ≤ Ce * ((n : ℝ) * (L : ℝ) ^ e + n) +
      (n : ℝ) ^ (-247 : ℝ)) :
    2 * logd - Real.log z + W * (Bsh / z + (1 + 3 * (n : ℝ) * D * Real.log q)) ≤
      (6 * Ce + 13 + 6 * Real.log q) * W * (n : ℝ) ^ (1 + e) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have h100 : (n : ℝ) ^ (-100 : ℝ) ≤ 1 / 2 := by
    calc
      (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hn2
  have hzh : 1 / 2 ≤ z := by linarith
  have hinvz : z⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hz (by norm_num)]
    linarith
  have hlogz : -1 ≤ Real.log z := by
    have h := Real.one_sub_inv_le_log_of_pos hz
    linarith
  let N := (n : ℝ) ^ (1 + e)
  have hNsplit : N = (n : ℝ) * (n : ℝ) ^ e := by
    dsimp only [N]
    rw [Real.rpow_add hnpos, Real.rpow_one]
  have hnN : (n : ℝ) ≤ N := by
    rw [hNsplit]
    exact le_mul_of_one_le_right hnpos.le (Real.one_le_rpow hn1 he)
  have hN1 : 1 ≤ N := hn1.trans hnN
  have hsmall : (n : ℝ) ^ (-247 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hwidth : (n : ℝ) ^ (3 / 5 : ℝ) ≤ N :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hLpower : (L : ℝ) ^ e ≤ (n : ℝ) ^ e :=
    Real.rpow_le_rpow (Nat.cast_nonneg L) (Nat.cast_le.mpr hL) he
  have hshell : (n : ℝ) * (L : ℝ) ^ e + n ≤ 2 * N := by
    have h := mul_le_mul_of_nonneg_left hLpower hnpos.le
    rw [← hNsplit] at h
    linarith
  have hB : Bsh ≤ 2 * (Ce + 1) * N := by
    have h := mul_le_mul_of_nonneg_left hshell hCe
    nlinarith
  have hBz : Bsh / z ≤ 4 * (Ce + 1) * N := by
    rw [div_le_iff₀ hz]
    have h := mul_le_mul_of_nonneg_left hzh
      (show 0 ≤ 4 * (Ce + 1) * N by positivity)
    nlinarith
  have hnD : (n : ℝ) * D ≤ 2 * N := by
    calc
      (n : ℝ) * D ≤ (n : ℝ) * (2 * (n : ℝ) ^ e) :=
        mul_le_mul_of_nonneg_left hDpower hnpos.le
      _ = 2 * N := by rw [hNsplit]; ring
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hnD1 : (1 : ℝ) ≤ (n : ℝ) * D :=
    one_le_mul_of_one_le_of_one_le hn1 hD1
  have hexc : 1 + 3 * (n : ℝ) * D * Real.log q ≤
      2 * (1 + 3 * Real.log q) * N := by
    have h := mul_le_mul_of_nonneg_right hnD (by linarith : 0 ≤ 1 + 3 * Real.log q)
    nlinarith
  have hd : 2 * logd - Real.log z ≤ (2 * Ce + 7) * N := by
    have h := le_abs_self (logd - St)
    nlinarith
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hterminal := mul_le_mul_of_nonneg_left (add_le_add hBz hexc) hW0
  have hhead : (2 * Ce + 7) * N ≤ (2 * Ce + 7) * (W * N) :=
    mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (by linarith) hW) (by positivity)
  calc
    2 * logd - Real.log z + W * (Bsh / z + (1 + 3 * (n : ℝ) * D * Real.log q)) ≤
        (2 * Ce + 7) * (W * N) + W *
          (4 * (Ce + 1) * N + 2 * (1 + 3 * Real.log q) * N) :=
      add_le_add (hd.trans hhead) hterminal
    _ = _ := by dsimp only [N]; ring

/-- The literal selected-density numerator is reduced to the two principal
rounded-scale terms, with its replica remainder still displayed. The scalar
coefficient `G` is the actual entropy-transport coefficient, bounded by the
accepted common logarithmic-power cap.
Source: `08-scanner.tex`, lines 480–490. -/
theorem selectedDensity_budget_le_principal
    {n m : ℕ} {W a ε C₁ Cr Ct e Cl B G R : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hW : 0 < W) (ha : 0 ≤ a)
    (hε : 0 < ε) (hC : 0 < C₁) (hCr : 0 ≤ Cr) (hCt : 0 ≤ Ct)
    (hB : B ≤ Cr * W * (n : ℝ) ^ (1 + e))
    (hG : G ≤ Ct * Real.log (n : ℝ) ^ Cl) :
    (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)) *
        (B + ((2 * n * m : ℕ) : ℝ) * G * W * a ^ (1 / 4 : ℝ) + R) ≤
      (2 * (C₁ + 1) * (Cr + 2 * Ct)) *
          ((n : ℝ) ^ e / (m : ℝ) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε +
        (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)) * R := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hquarter : 0 ≤ a ^ (1 / 4 : ℝ) := Real.rpow_nonneg ha _
  have hcoefficient : 0 ≤ 2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε) :=
    by positivity
  have htransport : ((2 * n * m : ℕ) : ℝ) * G * W * a ^ (1 / 4 : ℝ) ≤
      ((2 * n * m : ℕ) : ℝ) * (Ct * Real.log (n : ℝ) ^ Cl) * W *
        a ^ (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg _)) hW.le) hquarter
  have hprincipal : Cr * ((n : ℝ) ^ e / (m : ℝ)) +
      2 * Ct * (a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) ≤
      (Cr + 2 * Ct) *
        ((n : ℝ) ^ e / (m : ℝ) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) := by
    nlinarith [mul_nonneg hCr (mul_nonneg hquarter (Real.rpow_nonneg hlog Cl)),
      mul_nonneg hCt (div_nonneg (Real.rpow_nonneg hnr.le e) hmr.le)]
  calc
    (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)) *
        (B + ((2 * n * m : ℕ) : ℝ) * G * W * a ^ (1 / 4 : ℝ) + R) ≤
        (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)) *
          (Cr * W * (n : ℝ) ^ (1 + e) +
            ((2 * n * m : ℕ) : ℝ) * (Ct * Real.log (n : ℝ) ^ Cl) * W *
              a ^ (1 / 4 : ℝ) + R) :=
      mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add hB htransport) le_rfl)
        hcoefficient
    _ = (2 * (C₁ + 1) / ε) *
        (Cr * ((n : ℝ) ^ e / (m : ℝ)) +
          2 * Ct * (a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl)) +
          (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)) * R := by
      rw [Real.rpow_add hnr, Real.rpow_one]
      push_cast
      field_simp [hW.ne', hnr.ne', hmr.ne', hε.ne']
    _ ≤ (2 * (C₁ + 1) / ε) * ((Cr + 2 * Ct) *
        ((n : ℝ) ^ e / (m : ℝ) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl)) +
          (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)) * R :=
      _root_.add_le_add (mul_le_mul_of_nonneg_left hprincipal (by positivity)) le_rfl
    _ = _ := by ring

end TNLean.PEPS.AreaLaw.Scan
end

end

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- The rounded window estimate gives the source defect density, without
any additional decay margin or a polynomial upper bound on the weight.
Source: Proposition 9.2, `scanner:density-output` and lines 480–490. -/
theorem ScannerExponents.selectedDensity_budget_le_delta
    (X : ScannerExponents) {n : ℕ} {Cscale W C₁ Cr Ct Cl B G R : ℝ}
    (hscale : ScaleFacts X n Cscale) (hW : 0 < W) (hC₁ : 0 < C₁)
    (hCr : 0 ≤ Cr) (hCt : 0 ≤ Ct)
    (hB : B ≤ Cr * W * (n : ℝ) ^ (1 + X.e))
    (hG : G ≤ Ct * Real.log (n : ℝ) ^ Cl) :
    let a := X.a W n
    let ε := X.eps n
    let c := 2 * (C₁ + 1) /
      (W * ((n * X.m n : ℕ) : ℝ) * (ε / 2))
    c * (B + ((2 * n * X.m n : ℕ) : ℝ) * G * W * a ^ (1 / 4 : ℝ) + R) ≤
      X.delta W (4 * (C₁ + 1) * (Cr + 2 * Ct) * Cscale) Cl n + c * R := by
  have hprincipal := selectedDensity_budget_le_principal
    (Nat.lt_of_lt_of_le (by decide : 0 < 2) hscale.two_le_n)
    (Nat.lt_of_lt_of_le (by decide : 0 < 1) hscale.one_le_m) hW
    (show 0 ≤ X.a W n from div_nonneg hW.le (Nat.cast_nonneg _))
    (half_pos hscale.eps_pos) hC₁ hCr hCt hB hG (R := R)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr (Nat.le_trans (by decide) hscale.two_le_n))
  have hsum := add_le_add hscale.pow_e_div_m_le
    (le_mul_of_one_le_left
      (mul_nonneg
        (Real.rpow_nonneg (show 0 ≤ X.a W n from div_nonneg hW.le (Nat.cast_nonneg _))
          (1 / 4 : ℝ))
        (Real.rpow_nonneg hlog Cl)) hscale.one_le_C₁)
  refine hprincipal.trans (_root_.add_le_add ?_ le_rfl)
  refine (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ 2 * (C₁ + 1) * (Cr + 2 * Ct) by positivity))
    (half_pos hscale.eps_pos).le).trans ?_
  dsimp only [ScannerExponents.delta]
  exact le_of_eq (by ring)

end TNLean.PEPS.AreaLaw.Scan
end

end

section

noncomputable section

open Filter
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- The raw actual-selector density budget has the final source power while
preserving all propositions attached to its original selected point. The size
threshold precedes every physical scalar and replica remainder; the replica
threshold is chosen afterward for that fixed physical instance.
Source: `08-scanner.tex`, lines 457–490 and 839–865. -/
theorem exists_final_selectedDensity_le
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
            density k x p ≤ ε ∧ keep k x p := by
  let Cr := 6 * Ce + 13 + 6 * Real.log q
  let C := 2 * (C₁ + 1) * (Cr + 2 * Ct)
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hCr : 0 ≤ Cr := by dsimp only [Cr]; positivity
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨N, hN, hprincipal⟩ :=
    exists_final_principalDensity_le_rpow (C := 2 * C) (Cl := Cl) (by positivity)
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
  have hhalf : C * ((n : ℝ) ^ e / (m : ℝ) +
      a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε ≤ ε / 2 := by
    have hdouble := hprincipalN W hW hWupper
    change 2 * C * ((n : ℝ) ^ e / (m : ℝ) +
      a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε ≤ ε at hdouble
    have hdouble' : 2 * (C * ((n : ℝ) ^ e / (m : ℝ) +
        a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε) ≤ ε := by
      convert hdouble using 1
      ring
    linarith only [hdouble']
  let coeff := 2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)
  have hrem : Tendsto (fun k ↦ coeff * R k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hR.const_mul coeff
  have hremSmall : ∀ᶠ k : ℕ in atTop, coeff * R k ≤ ε / 2 :=
    ((tendsto_order.mp hrem).2 (ε / 2) (by positivity)).mono fun _ h ↦ h.le
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
end

end
