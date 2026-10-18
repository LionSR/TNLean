/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadHistoryPowerBound
import TNLean.PEPS.AreaLaw.Scan.BadChargeRatioBound
import TNLean.PEPS.AreaLaw.Scan.RadiusAsymptotics

/-!
# Arbitrary inverse-power decay of the actual finite bad-history bound

The radius is the rounded squared logarithm, the lookahead and window are
rounded powers, and the charge capacity is the source ceiling. Every constant
and every asymptotic threshold is chosen before the finite lattice, target,
label family, and actual scanner. No eventual scale comparison or probability
estimate is an input. The threshold is given explicitly by `badHistoryThreshold`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 9.1, `08-scanner.tex`, lines 309–329, at `openai/math@adc7f124`.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

universe u v

/-- The number `J = ⌈(p + 8) / (κ / 2)⌉₊` of charge-ratio factors in the geometric bad tail
that gives decay `n^{-p}` after the polynomial prefactor `n^8` (Lemma 9.1,
`08-scanner.tex`, lines 309–329). -/
noncomputable def badHistoryTailCount (kappa p : ℝ) : ℕ :=
  ⌈(p + 8) / (kappa / 2)⌉₊

/-- The explicit threshold of the bad-history bound of Lemma 9.1: the rounded-radius
thresholds for `117 e μ / (2 C₁) r₀³ ≤ n^{κ/2}` and `4 J r₀ ≤ n^κ`, and `n ≥ 8 (C_t + 1)`
(`08-scanner.tex`, lines 309–329). -/
noncomputable def badHistoryThreshold (kappa Cr C1 Ct : ℝ) (multiplicity : ℕ) (p : ℝ) : ℕ :=
  max (roundedLogRadiusThreshold Cr (kappa / 2) (117 * Real.exp 1 * multiplicity / (2 * C1)) 3)
    (max (roundedLogRadiusThreshold Cr kappa (4 * badHistoryTailCount kappa p) 1)
      ⌈8 * (Ct + 1)⌉₊)

/-- The bad-history threshold is at least `3`. -/
theorem three_le_badHistoryThreshold (kappa Cr C1 Ct : ℝ) (multiplicity : ℕ) (p : ℝ) :
    3 ≤ badHistoryThreshold kappa Cr C1 Ct multiplicity p :=
  le_trans (by simp [roundedLogRadiusThreshold]) (le_max_left _ _)

/-- The finite expression proved from actual ancestry is at most `n^{-p}` at every `n` from
the explicit threshold `badHistoryThreshold kappa Cr C1 Ct multiplicity p` on, uniformly in
the scanner and target (Lemma 9.1, `08-scanner.tex`, lines 309–329). -/
theorem badHistory_bound_le_rpow_of_threshold_le
    {ell kappa mu Cr C1 Ct : ℝ} (hell : 0 < ell) (hkappa : 0 < kappa)
    (hmu : mu < 1 - ell) (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (p : ℝ) {n : ℕ}
    (hthr : badHistoryThreshold kappa Cr C1 Ct multiplicity p ≤ n) :
    ∀ (V : Type u) (I : Type v) (S : CollarScan V I) (t : ℕ),
      S.n = n → S.m = ⌊(n : ℝ) ^ mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ kappa⌉₊ → S.r₀ = roundedLogRadius Cr n →
      S.M = ⌈C1 * n * S.D⌉₊ → (t : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      ((S.K * 2 * (t + S.n * ⌊(n : ℝ) ^ (1 - ell)⌋₊) *
        (n * S.m + 1) : ℕ) : ℝ) * S.geometricBadTail (n * S.m) multiplicity ≤
        (n : ℝ) ^ (-p) := by
  set J := badHistoryTailCount kappa p
  have hJ : (p + 8) / (kappa / 2) ≤ (J : ℝ) := Nat.le_ceil _
  have hJ' : p + 8 ≤ kappa / 2 * (J : ℝ) := by
    have := (div_le_iff₀ (by positivity : 0 < kappa / 2)).mp hJ
    linarith
  have hn3 : 3 ≤ n := (three_le_badHistoryThreshold _ _ _ _ _ _).trans hthr
  simp only [badHistoryThreshold, max_le_iff] at hthr
  obtain ⟨hcube, hcut, hc⟩ := hthr
  have hcube := const_mul_roundedLogRadius_pow_le_rpow_of_threshold_le hCr.le
    (show 0 < kappa / 2 by positivity) _ 3 hcube
  have hcut := const_mul_roundedLogRadius_pow_le_rpow_of_threshold_le hCr.le hkappa _ 1 hcut
  rw [pow_one] at hcut
  have hc : 8 * (Ct + 1) ≤ (n : ℝ) := Nat.ceil_le.mp hc
  have hr := one_le_roundedLogRadius_of_two_le hCr (show 2 ≤ n by omega)
  have hn : 1 ≤ n := by omega
  intro V I S t hSn hm hK hD hR hM ht
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hnNat : 0 < S.n := by omega
  have hDpos : 0 < S.D := by
    rw [hD]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos _)
  have hDR : (n : ℝ) ^ kappa ≤ S.D := by rw [hD]; exact Nat.le_ceil _
  have hcap : C1 * S.n * S.D ≤ S.M := by rw [hSn, hM]; exact Nat.le_ceil _
  have hratio : S.badChargeRatio multiplicity ≤ (n : ℝ) ^ (-(kappa / 2)) := by
    calc
      _ ≤ (117 * Real.exp 1 * multiplicity / (2 * C1)) *
          (S.r₀ : ℝ) ^ 3 / S.D :=
        S.badChargeRatio_le_radius_cube multiplicity hC1 hnNat hDpos (hR ▸ hr) hcap
      _ ≤ (n : ℝ) ^ (kappa / 2) / (n : ℝ) ^ kappa := by
        rw [hR]
        gcongr
      _ = _ := by rw [← Real.rpow_sub hnpos]; congr 1; ring
  have hcutNat : 4 * S.r₀ * J ≤ S.D := by
    have hh : (4 : ℝ) * S.r₀ * J ≤ S.D := by rw [hR]; nlinarith [hcut.trans hDR]
    exact_mod_cast hh
  have htail := S.geometricBadTail_le_power (n * S.m) multiplicity J hnR
    (by positivity : 0 ≤ kappa / 2) hcutNat hratio
  obtain ⟨hL, hm'⟩ := CollarScan.source_lengths_le hn hell.le (by linarith : mu ≤ 1)
  have hKn : S.K ≤ n := by rw [hK]; exact (Nat.div_le_self _ _).trans hL
  have hmn : S.m ≤ n := by rwa [hm]
  have hpref := CollarScan.badHistory_prefactor_le hn hKn hL hmn hCt ht
  rw [hSn]
  calc
    _ ≤ ((S.K * 2 * (t + n * ⌊(n : ℝ) ^ (1 - ell)⌋₊) *
          (n * S.m + 1) : ℕ) : ℝ) *
          ((n * S.m + 1 : ℕ) * (n : ℝ) ^ (-(kappa / 2) * J)) := by
      exact mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ 8 * (Ct + 1) * (n : ℝ) ^ 7 * (n : ℝ) ^ (-(kappa / 2) * J) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hpref (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ _ := CollarScan.badHistory_power_le hnR hc hJ'

/-- The finite expression proved from actual ancestry is smaller than every
fixed inverse power at the source scales, uniformly in the scanner and target. -/
theorem eventually_badHistory_bound_le_rpow
    {ell kappa mu Cr C1 Ct : ℝ} (hell : 0 < ell) (hkappa : 0 < kappa)
    (hmu : mu < 1 - ell) (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type u) (I : Type v) (S : CollarScan V I) (t : ℕ),
      S.n = n → S.m = ⌊(n : ℝ) ^ mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ kappa⌉₊ → S.r₀ = roundedLogRadius Cr n →
      S.M = ⌈C1 * n * S.D⌉₊ → (t : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      ((S.K * 2 * (t + S.n * ⌊(n : ℝ) ^ (1 - ell)⌋₊) *
        (n * S.m + 1) : ℕ) : ℝ) * S.geometricBadTail (n * S.m) multiplicity ≤
        (n : ℝ) ^ (-p) :=
  eventually_atTop.2 ⟨_, fun _ => badHistory_bound_le_rpow_of_threshold_le hell hkappa hmu
    hCr hC1 hCt multiplicity p⟩

end TNLean.PEPS.AreaLaw.Scan
