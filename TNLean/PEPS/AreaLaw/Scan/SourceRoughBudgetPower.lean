/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TargetEntropyTransfer
import TNLean.PEPS.AreaLaw.SelectedSchmidtEntropyBounds

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
-/

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
      <;> ring
    _ ≤ (2 * (C₁ + 1) / ε) * ((Cr + 2 * Ct) *
        ((n : ℝ) ^ e / (m : ℝ) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Cl)) +
          (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * ε)) * R :=
      _root_.add_le_add (mul_le_mul_of_nonneg_left hprincipal (by positivity)) le_rfl
    _ = _ := by ring

end TNLean.PEPS.AreaLaw.Scan
