/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapComparisonBudget
import TNLean.PEPS.AreaLaw.Scan.TargetEntropyTransfer

/-!
# The restored rough comparison has the improved entropy power

This numerical bridge includes the exact typical mass correction, whole-prefix
budget, mismatch cost and original-state continuity error. It is used only
after the physical rough comparisons and fixed-instance replica limit. The
coefficient is `bootstrapRestoredBudgetCoefficient` and the threshold is
`bootstrapComparisonBudgetThreshold`.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 755--792,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Validation and inherited-dependency scope:
`docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit base coefficient `8 C_e + 12 log q + 30` of the restored rough budget: it
dominates every term of the budget by the shell, separation, typical-window and
binary-entropy costs of the comparison budget (`08-scanner.tex`, lines 755--792). -/
noncomputable def bootstrapRestoredBudgetBaseCoefficient (q : ℕ) (Ce : ℝ) : ℝ :=
  8 * Ce + 12 * Real.log q + 30

/-- The explicit output coefficient `(8 C_e + 12 log q + 30) (5 + log 2 / 4)` of the restored
rough budget (`08-scanner.tex`, lines 755--792). -/
noncomputable def bootstrapRestoredBudgetCoefficient (q : ℕ) (Ce : ℝ) : ℝ :=
  bootstrapRestoredBudgetBaseCoefficient q Ce * (5 + Real.log 2 / 4)

/-- The explicit restored rough budget is bounded by the improved power with the explicit
coefficient `bootstrapRestoredBudgetCoefficient q Ce`, at every `n` from the explicit
threshold `bootstrapComparisonBudgetThreshold e₀` on, uniformly in the current exponent.
Source: `08-scanner.tex`, lines 755--792. -/
theorem bootstrap_restored_entropy_budget_of_threshold_le
    {e₀ : ℝ} (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1)
    {q : ℕ} (hq : 1 ≤ q) (Ce : ℝ) (hCe : 0 ≤ Ce) {n : ℕ}
    (hthr : bootstrapComparisonBudgetThreshold e₀ ≤ n) :
    let ell := BootstrapParameters.ell e₀
    let L := Nat.floor ((n : ℝ) ^ (1 - ell))
    let m := Nat.floor ((n : ℝ) ^ BootstrapParameters.mu e₀)
    let K := L / (8 * m)
    let D := Nat.ceil ((n : ℝ) ^ BootstrapParameters.kappa e₀)
    let a := 4 / (K : ℝ)
    ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
    ∀ S z τ : ℝ, 0 < z → 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z →
      0 ≤ τ → τ ≤ 1 →
      S ≤ 7 * ((n : ℝ) ^ (3 / 5 : ℝ) - Real.log z) - Real.log z +
        4 * (Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ)) / z +
        4 * (1 + 3 * (n : ℝ) * D * Real.log q) + 6 * Real.binEntropy τ / a +
        (n : ℝ) ^ (-247 : ℝ) →
      S ≤ bootstrapRestoredBudgetCoefficient q Ce * (n : ℝ) ^ (1 + (1 - ell) * e) := by
  let Cb := bootstrapRestoredBudgetBaseCoefficient q Ce
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hCbdef : Cb = 8 * Ce + 12 * Real.log q + 30 := rfl
  have hCb : 0 < Cb := by rw [hCbdef]; positivity
  intro ell L m K D a e he hee₀ S z τ hz hmass hτ hτ1 hS
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hthr
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hK, ha, hcost⟩ := bootstrap_comparison_budget_bound_of_threshold_le he₀ he₀₁ hthr
  have htail : (n : ℝ) ^ (-100 : ℝ) ≤ 1 / 2 := by
    calc
      _ ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hn2r
  have hzh : 1 / 2 ≤ z := by linarith
  have hinvz : z⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hz (by norm_num)]
    linarith
  have hlogz : -1 ≤ Real.log z := by
    linarith [Real.one_sub_inv_le_log_of_pos hz]
  have hsmall : (n : ℝ) ^ (-247 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hBz : (Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ)) / z ≤
      2 * (Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + 1) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hinvz (by positivity)
      _ ≤ _ := by nlinarith
  have hD : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hnD : (n : ℝ) ≤ (n : ℝ) * D := le_mul_of_one_le_right hnpos.le hDr
  have htau : 0 ≤ Real.binEntropy τ / a :=
    div_nonneg (Real.binEntropy_nonneg hτ hτ1) ha.le
  have hpre : S ≤ 8 * Ce * ((n : ℝ) * (L : ℝ) ^ e) +
      (8 * Ce + 12 * Real.log q) * ((n : ℝ) * D) +
      7 * (n : ℝ) ^ (3 / 5 : ℝ) + 6 * (Real.binEntropy τ / a) + 21 := by
    simp only [mul_div_assoc] at hS
    nlinarith [mul_le_mul_of_nonneg_left hnD hCe]
  have hsum : S ≤ Cb * ((n : ℝ) * (L : ℝ) ^ e + (n : ℝ) * D +
      (n : ℝ) ^ (3 / 5 : ℝ) + Real.binEntropy τ / a + 1) := by
    have h1 := mul_nonneg (show 0 ≤ Cb - 8 * Ce by linarith)
      (show 0 ≤ (n : ℝ) * (L : ℝ) ^ e by positivity)
    have h2 := mul_nonneg (show 0 ≤ Cb - (8 * Ce + 12 * Real.log q) by
      linarith) (show 0 ≤ (n : ℝ) * D by positivity)
    have h3 := mul_nonneg (show 0 ≤ Cb - 7 by linarith)
      (Real.rpow_nonneg hnpos.le (3 / 5 : ℝ))
    have h4 := mul_nonneg (show 0 ≤ Cb - 6 by linarith) htau
    have h5 : 21 ≤ Cb := by linarith
    nlinarith only [hpre, h1, h2, h3, h4, h5]
  calc
    S ≤ Cb * ((n : ℝ) * (L : ℝ) ^ e + (n : ℝ) * D +
        (n : ℝ) ^ (3 / 5 : ℝ) + Real.binEntropy τ / a + 1) := hsum
    _ ≤ Cb * ((5 + Real.log 2 / 4) * (n : ℝ) ^ (1 + (1 - ell) * e)) :=
      mul_le_mul_of_nonneg_left (hcost e he hee₀ τ) hCb.le
    _ = _ := by rw [bootstrapRestoredBudgetCoefficient]; ring

/-- The explicit restored rough budget is bounded by the improved power,
uniformly in the current exponent. Source: `08-scanner.tex`, lines 755--792. -/
theorem exists_bootstrap_restored_entropy_budget
    {e₀ : ℝ} (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1)
    {q : ℕ} (hq : 1 ≤ q) (Ce : ℝ) (hCe : 0 ≤ Ce) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let ell := BootstrapParameters.ell e₀
      let L := Nat.floor ((n : ℝ) ^ (1 - ell))
      let m := Nat.floor ((n : ℝ) ^ BootstrapParameters.mu e₀)
      let K := L / (8 * m)
      let D := Nat.ceil ((n : ℝ) ^ BootstrapParameters.kappa e₀)
      let a := 4 / (K : ℝ)
      ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
      ∀ S z τ : ℝ, 0 < z → 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z →
        0 ≤ τ → τ ≤ 1 →
        S ≤ 7 * ((n : ℝ) ^ (3 / 5 : ℝ) - Real.log z) - Real.log z +
          4 * (Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ)) / z +
          4 * (1 + 3 * (n : ℝ) * D * Real.log q) + 6 * Real.binEntropy τ / a +
          (n : ℝ) ^ (-247 : ℝ) →
        S ≤ C * (n : ℝ) ^ (1 + (1 - ell) * e) :=
  ⟨_, mul_pos (show (0 : ℝ) < 8 * Ce + 12 * Real.log q + 30 by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)]) (by positivity),
    _, le_max_left _ _,
    fun _ => bootstrap_restored_entropy_budget_of_threshold_le he₀ he₀₁ hq Ce hCe⟩

end TNLean.PEPS.AreaLaw.Scan
