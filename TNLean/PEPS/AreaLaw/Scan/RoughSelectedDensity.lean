/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceRoughBudgetPower
import TNLean.PEPS.AreaLaw.Scan.Budgets

/-!
# Principal density at the unchanged rough-selected point

The literal rough endpoint budget and source entropy estimates reduce the
selected density to the principal expression used by the bootstrap energy
estimate. Its coefficient and scale threshold precede the current entropy
exponent and every physical scalar. Only the replica threshold depends on
that fixed instance. All conclusions attached to the selected point survive.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 457--490 and
693--755, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Validation and inherited-dependency scope:
`docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

noncomputable section
open Filter
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- The actual rough selection numerator gives the bootstrap principal density,
with no sharp-margin condition. The current exponent is only required to
control the fixed separation exponent. Source: `08-scanner.tex`, lines 480--490
and 731--755. -/
theorem ScannerExponents.exists_rough_selectedDensity_principal
    (F : ScannerExponents) {q : ℕ} (hq : 1 ≤ q) (Ce C₁ Ct Cl : ℝ)
    (hCe : 0 ≤ Ce) (hC : 0 < C₁) (hCt : 0 ≤ Ct) :
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := F.L n
      let m := F.m n
      let K := F.K n
      let D := F.D n
      let a := 4 / (K : ℝ)
      let ε := (n : ℝ) ^ (-F.nu)
      ∀ e : ℝ, F.kappa ≤ e →
      let δ := Cδ * ε⁻¹ *
        ((n : ℝ) ^ (e - F.mu) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl)
      ∀ St logd z Bsh G : ℝ, 0 < z → 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z →
        St ≤ Ce * (n : ℝ) ^ (1 + e) + (n : ℝ) ^ (-247 : ℝ) →
        |logd - St| ≤ (n : ℝ) ^ (3 / 5 : ℝ) - Real.log z →
        Bsh ≤ Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ) →
        G ≤ Ct * Real.log (n : ℝ) ^ Cl →
        let Brough := 2 * logd - Real.log z + 4 *
          (Bsh / z + (1 + 3 * (n : ℝ) * D * Real.log q))
        ∀ R : ℕ → ℝ, Tendsto R atTop (𝓝 0) →
        ∀ {α : Type*} (density : ℕ → α → ℝ → ℝ) (keep : ℕ → α → ℝ → Prop)
          (p₀ p₁ : ℝ),
          (∀ᶠ k : ℕ in atTop, ∃ x : α, ∃ p ∈ Set.Icc p₀ p₁,
            density k x p ≤ (2 * (C₁ + 1) / (4 * ((n * m : ℕ) : ℝ) * ε)) *
              (Brough + ((2 * n * m : ℕ) : ℝ) * G * 4 * a ^ (1 / 4 : ℝ) + R k) ∧
                keep k x p) →
          ∀ᶠ k : ℕ in atTop, ∃ x : α, ∃ p ∈ Set.Icc p₀ p₁,
            density k x p ≤ δ ∧ keep k x p := by
  let Cr := 6 * Ce + 13 + 6 * Real.log q
  let C := 2 * (C₁ + 1) * (Cr + 2 * Ct)
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hCr : 0 < Cr := by dsimp only [Cr]; positivity
  have hC0 : 0 < C := by dsimp only [C]; positivity
  obtain ⟨_, hscale⟩ := eventually_scaleFacts F
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hscale.and (eventually_le_natCast_rpow (F.kappa_pos.trans F.kappa_lt_mu) 2))
  refine ⟨4 * C, by positivity, N, (hN N le_rfl).1.two_le_n, ?_⟩
  intro n hn L m K D a ε e he δ St logd z Bsh G hz hmass hSt hlogd hBsh hG
    Brough R hR α density keep p₀ p₁ hselected
  have hf := (hN n hn).1
  have hn2 := hf.two_le_n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hm : 0 < m := zero_lt_one.trans_le hf.one_le_m
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hε : 0 < ε := Real.rpow_pos_of_pos hnpos _
  have he0 : 0 ≤ e := F.kappa_pos.le.trans he
  have hDpower : (D : ℝ) ≤ 2 * (n : ℝ) ^ e := by
    have hceil : (D : ℝ) < (n : ℝ) ^ F.kappa + 1 := Nat.ceil_lt_add_one (by positivity)
    have hκ1 := Real.one_le_rpow hn1 F.kappa_pos.le
    have hκe := Real.rpow_le_rpow_of_exponent_le hn1 he
    linarith
  have hrough : Brough ≤ Cr * 4 * (n : ℝ) ^ (1 + e) :=
    roughBudget_le_source_power hn2 hq he0 hCe (by norm_num) hf.L_le_n
      hf.one_le_D hDpower hz hmass hSt hlogd hBsh
  have hfloor : (n : ℝ) ^ F.mu / 2 ≤ m := half_le_floor (hN n hn).2
  have hquot : (n : ℝ) ^ e / (m : ℝ) ≤ 2 * (n : ℝ) ^ (e - F.mu) := by
    rw [Real.rpow_sub hnpos, div_le_iff₀ hmr]
    have hpow : 0 ≤ (n : ℝ) ^ e / (n : ℝ) ^ F.mu := by positivity
    have hcancel : (n : ℝ) ^ e / (n : ℝ) ^ F.mu * (n : ℝ) ^ F.mu =
        (n : ℝ) ^ e := div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hfloor hpow]
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos (mul_pos (by positivity) (inv_pos.mpr hε))
      (add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hnpos _)
        (mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg (Real.log_nonneg hn1) _)))
  have hhalf : C * ((n : ℝ) ^ e / (m : ℝ) +
      a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε ≤ δ / 2 := by
    have hterm : 0 ≤ a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl :=
      mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg (Real.log_nonneg hn1) _)
    calc
      _ ≤ C * (2 * ((n : ℝ) ^ (e - F.mu) +
          a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl)) / ε :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0.le) hε.le
      _ = δ / 2 := by dsimp only [δ]; rw [div_eq_mul_inv]; ring
  let coeff := 2 * (C₁ + 1) / (4 * ((n * m : ℕ) : ℝ) * ε)
  have hrem : Tendsto (fun k ↦ coeff * R k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hR.const_mul coeff
  have hremSmall : ∀ᶠ k : ℕ in atTop, coeff * R k ≤ δ / 2 :=
    ((tendsto_order.mp hrem).2 (δ / 2) (by positivity)).mono fun _ h ↦ h.le
  filter_upwards [hselected, hremSmall] with k hk hremK
  obtain ⟨x, p, hp, hQ, hx⟩ := hk
  refine ⟨x, p, hp, ?_, hx⟩
  have hbudget := selectedDensity_budget_le_principal
    (show 0 < n by omega) hm (by norm_num : (0 : ℝ) < 4) ha hε hC hCr.le hCt
      hrough hG (R := R k)
  have hbound := hQ.trans hbudget
  change density k x p ≤ C * ((n : ℝ) ^ e / (m : ℝ) +
    a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl) / ε + coeff * R k at hbound
  linarith

end TNLean.PEPS.AreaLaw.Scan
