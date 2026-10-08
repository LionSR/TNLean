/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs

/-!
# Scale arithmetic and comparator budgets of the scan

Elementary consequences of the scales `scanner:scales`, and the comparator inputs of
Proposition 9.2: the transfer of the entropy input from `Ω` to `\widetilde Ω`, the shell budget
`B_sh ≤ C (n L^e + n)`, the mismatch budget `B_exc ≤ C n D`, the marginal parameter
`𝓑 ≤ C n D (log n)^C`, and the terminal rough upper bound `≤ C W n^{1+e}`.

**Scope restriction (inputs as hypotheses):** the results of this module stated over `ScanData`
are proved from its fields, which record the conclusions of Lemma 9.1, Propositions 7.4
and 8.1, and Lemmas 2.1 and 2.3 for one scan rather than deriving them. Documented in
`docs/paper-gaps/arealaw2d_scanner_inputs.tex`.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.eventually_scaleFacts`
* `TNLean.PEPS.AreaLaw.Scan.ScanData.SXt_le`, `TNLean.PEPS.AreaLaw.Scan.ScanData.SQt_le`
* `TNLean.PEPS.AreaLaw.Scan.exists_budgets`

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  section file `08-scanner.tex`, lines 32–59 (scales), 386–391 (budgets in the statement of
  Proposition 9.2), 400–414 (entropy transfer and budgets), 462–470 (terminal bound).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open Filter


/-- A positive power of `n` eventually exceeds any bound. -/
lemma eventually_le_natCast_rpow {y : ℝ} (hy : 0 < y) (b : ℝ) :
    ∀ᶠ n : ℕ in atTop, b ≤ (n : ℝ) ^ y :=
  ((tendsto_rpow_atTop hy).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop b

/-- `⌊x⌋₊ ≥ x / 2` once `x ≥ 2`. -/
lemma half_le_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ ⌊x⌋₊ := by
  have := Nat.lt_floor_add_one x
  linarith

/-- The elementary scale facts hold for all sufficiently large `n` (`08-scanner.tex`,
lines 32–42, 469, 480, 519–520), with `C₁ = 32`. -/
theorem eventually_scaleFacts (X : ScannerExponents) :
    ∃ C₁ : ℝ, ∀ᶠ n in atTop, ScaleFacts X n C₁ := by
  refine ⟨32, ?_⟩
  have hμ : 0 < X.mu := X.kappa_pos.trans X.kappa_lt_mu
  have hℓ : 0 < 1 - X.ell := sub_pos.2 X.ell_lt_one
  have hℓμ : 0 < 1 - X.ell - X.mu := by linarith [X.mu_lt_one_sub_ell]
  filter_upwards [eventually_ge_atTop 2, eventually_le_natCast_rpow hμ 2,
    eventually_le_natCast_rpow hℓ 2, eventually_le_natCast_rpow hℓμ (16 * (X.W + 2))]
    with n hn hm hL hK
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hW := X.one_le_W
  have hm_le : (X.m n : ℝ) ≤ (n : ℝ) ^ X.mu := Nat.floor_le (by positivity)
  have hm_ge : (n : ℝ) ^ X.mu / 2 ≤ X.m n := half_le_floor hm
  have hL_le : (X.L n : ℝ) ≤ (n : ℝ) ^ (1 - X.ell) := Nat.floor_le (by positivity)
  have hL_ge : (n : ℝ) ^ (1 - X.ell) / 2 ≤ X.L n := half_le_floor hL
  have hm_pos : (0 : ℝ) < X.m n := by linarith
  have hsplit : (n : ℝ) ^ (1 - X.ell) = (n : ℝ) ^ (1 - X.ell - X.mu) * (n : ℝ) ^ X.mu := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hratio : (X.W + 2) * (8 * X.m n) ≤ (X.L n : ℝ) := by
    have h1 : (X.W + 2) * (8 * X.m n) ≤ (X.W + 2) * (8 * (n : ℝ) ^ X.mu) := by gcongr
    have h2 : (X.W + 2) * (8 * (n : ℝ) ^ X.mu) ≤ (n : ℝ) ^ (1 - X.ell) / 2 := by
      rw [hsplit]
      have := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ X.mu)
      linarith
    linarith
  have hdiv : (X.L n : ℝ) < X.K n * (8 * X.m n) + 8 * X.m n := by
    have h := Nat.lt_div_mul_add (a := X.L n) (b := 8 * X.m n) (by
      have : 0 < X.m n := by exact_mod_cast hm_pos
      omega)
    unfold ScannerExponents.K
    exact_mod_cast h
  have hK1 : X.W + 1 < X.K n := by
    by_contra h
    push Not at h
    have : (X.K n : ℝ) * (8 * X.m n) ≤ (X.W + 1) * (8 * X.m n) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    nlinarith
  have hKpos : (0 : ℝ) < X.K n := by linarith
  have hmK : (n : ℝ) ^ (1 - X.ell) ≤ 32 * (X.m n * X.K n) := by
    have : (24 : ℝ) * X.m n ≤ X.L n := by nlinarith
    nlinarith
  have hnL : (n : ℝ) = (n : ℝ) ^ X.ell * (n : ℝ) ^ (1 - X.ell) := by
    rw [← Real.rpow_add hn0]; simp
  have hκ1 : (1 : ℝ) ≤ (n : ℝ) ^ X.kappa := Real.one_le_rpow hn1 X.kappa_pos.le
  have hκe : (n : ℝ) ^ X.kappa ≤ (n : ℝ) ^ X.e :=
    Real.rpow_le_rpow_of_exponent_le hn1 X.kappa_le_e
  refine
    { two_le_n := hn
      one_le_K := by exact_mod_cast (show (1 : ℝ) ≤ X.K n by linarith)
      one_le_m := by exact_mod_cast (show (1 : ℝ) ≤ X.m n by linarith)
      one_le_D := Nat.one_le_iff_ne_zero.2 (by
        unfold ScannerExponents.D
        exact (Nat.ceil_pos.2 (by positivity)).ne')
      L_le_n := Nat.floor_le_of_le (by
        simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [X.ell_pos] :
          1 - X.ell ≤ 1))
      eps_pos := by unfold ScannerExponents.eps; positivity
      eps_lt_one := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith [X.nu_pos])
      a_le_one := by
        unfold ScannerExponents.a
        rw [div_le_one hKpos]; linarith
      one_le_C₁ := by norm_num
      pow_e_div_m_le := ?_
      D_le := ?_
      coefficient_le := ?_ }
  · rw [Real.rpow_sub hn0, div_le_iff₀ hm_pos]
    have ht : 0 ≤ (n : ℝ) ^ X.e / (n : ℝ) ^ X.mu := by positivity
    have hc : (n : ℝ) ^ X.e / (n : ℝ) ^ X.mu * (n : ℝ) ^ X.mu = (n : ℝ) ^ X.e :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hm_ge ht]
  · have : (X.D n : ℝ) < (n : ℝ) ^ X.kappa + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  · rw [div_le_iff₀ (by positivity)]
    calc X.W ^ 2 * n * (X.D n : ℝ) ^ 2
        = X.W ^ 2 * (X.D n : ℝ) ^ 2 * ((n : ℝ) ^ X.ell * (n : ℝ) ^ (1 - X.ell)) := by
          rw [← hnL]; ring
      _ ≤ X.W ^ 2 * (X.D n : ℝ) ^ 2 * ((n : ℝ) ^ X.ell * (32 * (X.m n * X.K n))) := by
          gcongr
      _ = _ := by ring


/-- The continuity cost `C √t (1 + C n² log q)` of Lemma 2.1 at trace distance
`t ≤ n^{-500}` is at most `n^{-247}` for all sufficiently large `n`. -/
lemma eventually_continuityCost_le (C lq : ℝ) (hC : 0 ≤ C) (hlq : 0 ≤ lq) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, t ≤ (n : ℝ) ^ (-500 : ℝ) →
      C * √t * (1 + C * (n : ℝ) ^ 2 * lq) ≤ (n : ℝ) ^ (-247 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (C * (1 + C * lq))] with n hn hnC t ht
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : √t ≤ (n : ℝ) ^ (-250 : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    rw [show (-250 : ℝ) * ((2 : ℕ) : ℝ) = -500 by norm_num]
    exact ht
  have hsplit :
      (n : ℝ) ^ (-247 : ℝ) = (n : ℝ) ^ (-250 : ℝ) * ((n : ℝ) * (n : ℝ) ^ 2) := by
    rw [← pow_succ', ← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have h1 : 1 + C * (n : ℝ) ^ 2 * lq ≤ (1 + C * lq) * (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hC hlq]
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-250 : ℝ) := by positivity
  calc C * √t * (1 + C * (n : ℝ) ^ 2 * lq)
      ≤ C * (n : ℝ) ^ (-250 : ℝ) * ((1 + C * lq) * (n : ℝ) ^ 2) := by
        have : 0 ≤ 1 + C * (n : ℝ) ^ 2 * lq := by positivity
        gcongr
    _ = (n : ℝ) ^ (-250 : ℝ) * ((C * (1 + C * lq)) * (n : ℝ) ^ 2) := by ring
    _ ≤ (n : ℝ) ^ (-250 : ℝ) * ((n : ℝ) * (n : ℝ) ^ 2) := by gcongr
    _ = _ := hsplit.symm

namespace ScanData

variable {X : ScannerExponents} {κ : ScanConstants}

/-- `log q ≥ 0`, as `q ≥ 2`. -/
lemma log_q_nonneg (κ : ScanConstants) : 0 ≤ Real.log κ.q :=
  Real.log_nonneg (by exact_mod_cast (by linarith [κ.two_le_q] : 1 ≤ κ.q))

/-- The truncation costs `O(n^{-247})` in the target entropy: the trace distance is
`O(n^{-500})` and the target has `O(n²)` sites (lines 400–403, Lemma 2.1). -/
theorem SXt_le (X : ScannerExponents) (κ : ScanConstants) :
    ∀ᶠ n in atTop, ∀ S : ScanData X κ n,
      S.SXt ≤ κ.Ce * (n : ℝ) ^ (1 + X.e) + (n : ℝ) ^ (-247 : ℝ) := by
  filter_upwards [eventually_continuityCost_le κ.C _ (by linarith [κ.one_le_C])
    (log_q_nonneg κ)] with n hn S
  have := hn _ S.traceDist_le
  have := S.continuity_X
  have := S.entropy_input_X
  have := le_abs_self (S.SXt - S.SX)
  linarith

/-- The truncation costs `O(n^{-247})` in every shell entropy (lines 400–403, Lemma 2.1). -/
theorem SQt_le (X : ScannerExponents) (κ : ScanConstants) :
    ∀ᶠ n in atTop, ∀ S : ScanData X κ n, ∀ j ≤ X.L n,
      S.SQt j ≤ κ.Ce * (n * (X.L n : ℝ) ^ X.e + n) + (n : ℝ) ^ (-247 : ℝ) := by
  filter_upwards [eventually_continuityCost_le κ.C _ (by linarith [κ.one_le_C])
    (log_q_nonneg κ)] with n hn S j hj
  have := hn _ S.traceDist_le
  have := S.continuity_Q j hj
  have := S.entropy_input_Q j hj
  have := le_abs_self (S.SQt j - S.SQ j)
  linarith

variable {n : ℕ} (S : ScanData X κ n)

/-- The marginal parameter: `𝓑 ≤ C' n D (log n)^{12}` once `log n ≥ 1` (lines 405–409). -/
lemma Bmarg_le_log_pow (hD : 1 ≤ X.D n) (hn : 1 ≤ n) (hlog : 1 ≤ Real.log n) :
    S.Bmarg ≤ (1 + κ.C * (κ.C + 2) ^ 6 * (1 + κ.C * Real.log κ.q) ^ 2) *
      (n * X.D n * Real.log n ^ 12) := by
  have hlq := log_q_nonneg κ
  have hC := κ.one_le_C
  have hR1 : (1 : ℝ) ≤ S.r0 + 1 := by simp
  have hR : (S.r0 + 1 : ℝ) ≤ (κ.C + 2) * Real.log n ^ 2 := by
    have := S.r0_le
    have : 1 ≤ Real.log n ^ 2 := one_le_pow₀ hlog
    nlinarith
  have hR2 : ((S.r0 : ℝ) + 1) ^ 2 ≤ (κ.C + 2) ^ 2 * Real.log n ^ 4 := by
    calc ((S.r0 : ℝ) + 1) ^ 2 ≤ ((κ.C + 2) * Real.log n ^ 2) ^ 2 := by gcongr
      _ = _ := by ring
  have hcc : (S.crossCount : ℝ) ≤ κ.C * n * X.D n * ((κ.C + 2) ^ 2 * Real.log n ^ 4) :=
    S.crossCount_le.trans (by gcongr)
  have hin : 1 + κ.C * ((S.r0 : ℝ) + 1) ^ 2 * Real.log κ.q ≤
      (1 + κ.C * Real.log κ.q) * ((κ.C + 2) ^ 2 * Real.log n ^ 4) := by
    have h1 : (1 : ℝ) ≤ ((S.r0 : ℝ) + 1) ^ 2 := one_le_pow₀ hR1
    have h2 : 0 ≤ κ.C * Real.log κ.q := by positivity
    calc 1 + κ.C * ((S.r0 : ℝ) + 1) ^ 2 * Real.log κ.q
        = 1 + κ.C * Real.log κ.q * ((S.r0 : ℝ) + 1) ^ 2 := by ring
      _ ≤ (1 + κ.C * Real.log κ.q) * ((S.r0 : ℝ) + 1) ^ 2 := by nlinarith
      _ ≤ _ := by gcongr
  have hin0 : 0 ≤ 1 + κ.C * ((S.r0 : ℝ) + 1) ^ 2 * Real.log κ.q := by positivity
  have hnD : (1 : ℝ) ≤ n * X.D n := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hn)
    (by exact_mod_cast hD)
  have hbig : (1 : ℝ) ≤ n * X.D n * Real.log n ^ 12 :=
    one_le_mul_of_one_le_of_one_le hnD (one_le_pow₀ hlog)
  calc S.Bmarg ≤ 1 + S.crossCount * (1 + κ.C * (S.r0 + 1) ^ 2 * Real.log κ.q) ^ 2 := S.Bmarg_le
    _ ≤ 1 + κ.C * n * X.D n * ((κ.C + 2) ^ 2 * Real.log n ^ 4) *
          ((1 + κ.C * Real.log κ.q) * ((κ.C + 2) ^ 2 * Real.log n ^ 4)) ^ 2 := by gcongr
    _ = 1 + κ.C * (κ.C + 2) ^ 6 * (1 + κ.C * Real.log κ.q) ^ 2 *
          (n * X.D n * Real.log n ^ 12) := by ring
    _ ≤ _ := by linarith

/-- The terminal rough upper bound in terms of the target entropy and budget bounds `B`, `E`
(lines 462–470, with `z ≥ 1/2` from Lemma 2.3, lines 411–414). -/
lemma terminalBound_le_of {B E : ℝ} (hB0 : 0 ≤ B) (hBsh : S.Bsh ≤ B) (hBexc : S.Bexc ≤ E)
    (hn : 2 ≤ n) :
    S.terminalBound ≤ 2 * (S.SXt + (n : ℝ) ^ (3 / 5 : ℝ) + 1) + 1 + X.W * (2 * B + E) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have h100 : (n : ℝ) ^ (-100 : ℝ) ≤ 1 / 2 := by
    calc (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hn2
  have hz := S.one_sub_le_z
  have hz0 := S.z_pos
  have hzh : 1 / 2 ≤ S.z := by linarith
  have hlogz0 : Real.log S.z ≤ 0 := Real.log_nonpos hz0.le S.z_le_one
  have hlogz1 : -1 ≤ Real.log S.z := by
    have := Real.one_sub_inv_le_log_of_pos hz0
    have : S.z⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hz0 (by norm_num)]; linarith
    linarith
  have habs : |Real.log S.z| ≤ 1 := by rw [abs_of_nonpos hlogz0]; linarith
  have hd := S.log_dstar_le
  have hd' := le_abs_self (Real.log S.dstar - S.SXt)
  rw [S.width_eq] at hd
  have hBz : S.Bsh / S.z ≤ 2 * B := by
    rw [div_le_iff₀ hz0]; nlinarith
  have hW : 0 ≤ X.W := by linarith [X.one_le_W]
  have hWB : X.W * (S.Bsh / S.z + S.Bexc) ≤ X.W * (2 * B + E) := by gcongr
  have : S.terminalBound = 2 * Real.log S.dstar - Real.log S.z +
      X.W * (S.Bsh / S.z + S.Bexc) := by
    unfold terminalBound; ring
  rw [this]
  linarith

end ScanData

/-- The comparator budgets of Proposition 9.2 (lines 386–391, proof lines 400–410) and the
terminal rough upper bound (lines 462–470): for all sufficiently large `n`, uniformly in the
scan data, `B_sh ≤ C (n L^e + n)`, `B_exc ≤ C n D`, `𝓑 ≤ C n D (log n)^{C_l}`, and
`2 log d_* - log z + 2sW(2B_sh/z + 2B_exc) ≤ C W n^{1+e}`. -/
theorem exists_budgets (X : ScannerExponents) (κ : ScanConstants) :
    ∃ C Cl : ℝ, ∀ᶠ n in atTop, ∀ S : ScanData X κ n,
      S.Bsh ≤ C * (n * (X.L n : ℝ) ^ X.e + n) ∧
      S.Bexc ≤ C * n * X.D n ∧
      S.Bmarg ≤ C * n * X.D n * Real.log n ^ Cl ∧
      S.terminalBound ≤ C * X.W * (n : ℝ) ^ (1 + X.e) := by
  obtain ⟨C₁, hC₁⟩ := eventually_scaleFacts X
  have hlq : 0 ≤ Real.log κ.q := ScanData.log_q_nonneg κ
  have hC : 1 ≤ κ.C := κ.one_le_C
  have hCe := κ.Ce_pos
  have hW := X.one_le_W
  obtain ⟨C1, hC1⟩ : ∃ c : ℝ, c = κ.Ce + 1 + Real.log κ.q := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ c : ℝ, c = 1 + κ.C * Real.log κ.q := ⟨_, rfl⟩
  obtain ⟨C3, hC3⟩ : ∃ c : ℝ,
    c = 1 + κ.C * (κ.C + 2) ^ 6 * (1 + κ.C * Real.log κ.q) ^ 2 := ⟨_, rfl⟩
  have hC10 : 0 ≤ C1 := by rw [hC1]; positivity
  have hC20 : 1 ≤ C2 := by rw [hC2]; nlinarith
  have hC30 : 0 ≤ C3 := by rw [hC3]; positivity
  refine ⟨C1 + C2 + C3 + (2 * κ.Ce + 7 + 4 * C1 + C2 * C₁), 12, ?_⟩
  filter_upwards [hC₁, ScanData.SXt_le X κ, ScanData.SQt_le X κ,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with n hF hSX hSQ hlog S
  have hC₁1 := hF.one_le_C₁
  have hC40 : 0 ≤ 2 * κ.Ce + 7 + 4 * C1 + C2 * C₁ := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hF.two_le_n
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hD1 : (1 : ℝ) ≤ X.D n := by exact_mod_cast hF.one_le_D
  have hnD : (1 : ℝ) ≤ n * X.D n := one_le_mul_of_one_le_of_one_le hn1 hD1
  have hsmall : (n : ℝ) ^ (-247 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hNsplit : (n : ℝ) ^ (1 + X.e) = n * (n : ℝ) ^ X.e := by
    rw [Real.rpow_add hn0, Real.rpow_one]
  have hne1 : (1 : ℝ) ≤ (n : ℝ) ^ X.e := Real.one_le_rpow hn1 X.e_pos.le
  have hnN : (n : ℝ) ≤ (n : ℝ) ^ (1 + X.e) := by rw [hNsplit]; nlinarith
  have hLe : (X.L n : ℝ) ^ X.e ≤ (n : ℝ) ^ X.e :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hF.L_le_n) X.e_pos.le
  have hnLe : (n : ℝ) * (X.L n : ℝ) ^ X.e ≤ (n : ℝ) ^ (1 + X.e) := by
    rw [hNsplit]; gcongr
  have hshell0 : 0 ≤ (n : ℝ) * (X.L n : ℝ) ^ X.e + n := by positivity
  have hBsh : S.Bsh ≤ C1 * (n * (X.L n : ℝ) ^ X.e + n) := by
    obtain ⟨j, hj, hB⟩ := S.Bsh_le
    have := hSQ S j hj
    have h0 : 0 ≤ (n : ℝ) * (X.L n : ℝ) ^ X.e := by positivity
    have : Real.log κ.q * n ≤ Real.log κ.q * ((n : ℝ) * (X.L n : ℝ) ^ X.e + n) := by
      gcongr; linarith
    rw [hC1]; nlinarith
  have hBexc : S.Bexc ≤ C2 * (n * X.D n) := by
    have := S.Bexc_le
    rw [hC2]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hBsh.trans (mul_le_mul_of_nonneg_right (by linarith) hshell0)
  · calc S.Bexc ≤ C2 * (n * X.D n) := hBexc
      _ ≤ (C1 + C2 + C3 + (2 * κ.Ce + 7 + 4 * C1 + C2 * C₁)) * (n * X.D n) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = _ := by ring
  · rw [show Real.log n ^ (12 : ℝ) = Real.log n ^ (12 : ℕ) by
      exact_mod_cast Real.rpow_natCast _ 12]
    have hpos : 0 ≤ (n : ℝ) * X.D n * Real.log n ^ 12 := by positivity
    calc S.Bmarg ≤ C3 * (n * X.D n * Real.log n ^ 12) := by
          rw [hC3]; exact S.Bmarg_le_log_pow hF.one_le_D (by have := hF.two_le_n; omega) hlog
      _ ≤ (C1 + C2 + C3 + (2 * κ.Ce + 7 + 4 * C1 + C2 * C₁)) *
            (n * X.D n * Real.log n ^ 12) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos
      _ = _ := by ring
  · set N := (n : ℝ) ^ (1 + X.e)
    have hN1 : 1 ≤ N := hn1.trans hnN
    have hw : (n : ℝ) ^ (3 / 5 : ℝ) ≤ N :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [X.e_pos])
    have hB0 : 0 ≤ C1 * (2 * N) := by positivity
    have hBsh' : S.Bsh ≤ C1 * (2 * N) := hBsh.trans (by gcongr; linarith)
    have hBexc' : S.Bexc ≤ C2 * C₁ * N := by
      have hD := hF.D_le
      calc S.Bexc ≤ C2 * (n * X.D n) := hBexc
        _ ≤ C2 * (n * (C₁ * (n : ℝ) ^ X.e)) := by gcongr
        _ = C2 * C₁ * N := by simp only [N, hNsplit]; ring
    have h := S.terminalBound_le_of hB0 hBsh' hBexc' hF.two_le_n
    have hS := hSX S
    have hWN : N ≤ X.W * N := le_mul_of_one_le_left (by linarith) hW
    have h1 : (2 * κ.Ce + 7) * N ≤ (2 * κ.Ce + 7) * (X.W * N) := by gcongr
    have h2 : 0 ≤ (C1 + C2 + C3) * (X.W * N) := by positivity
    have hfin : (C1 + C2 + C3 + (2 * κ.Ce + 7 + 4 * C1 + C2 * C₁)) * X.W * N =
        (C1 + C2 + C3) * (X.W * N) + (2 * κ.Ce + 7) * (X.W * N) +
          X.W * (2 * (C1 * (2 * N)) + C2 * C₁ * N) := by ring
    rw [hfin]
    nlinarith

end TNLean.PEPS.AreaLaw.Scan
