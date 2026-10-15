/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FinalSharpScalarBounds

/-!
# The explicit source error budget after the replica limit

The literal scalar expression delivered by the same-point entropy comparison
is bounded term by term. Target and shell entropy at exponent `boxError` are
explicit antecedents. In particular this module does not prove that preceding
safe-box estimate or its bootstrap step.

The final parameters are unchanged: `W = n^(1/20000)` and
`tau = n^(-1/4000)`. The exact selected-mass, window, marginal and trace
budgets remain visible. The replica remainder has already been removed at a
fixed physical instance before this scalar expression is used.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 839--942,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
See `docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The complete scalar error delivered by the actual entropy comparison,
including the original-state continuity cost. `dlog` is `log(e dim X)`. -/
noncomputable def finalSharpError (n : ℕ)
    (a C₀ B St Bsh z lq t dlog : ℝ) : ℝ :=
  let W := (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
  let τ := (n : ℝ) ^ (-(1 / 4000 : ℝ))
  let c := (n : ℝ) ^ (3 / 5 : ℝ) - Real.log z
  let H := 4 * St + 2 * c + 2 * Bsh + 6 * (n : ℝ) *
    (Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ)) : ℝ) * lq
  (4 * St + 4 * c - 2 * Real.log z) / W +
    (τ + (n : ℝ) ^ (-(1 / 2000 : ℝ)) / τ) * H +
    (3 + 1 / a) * Real.binEntropy τ + 37 * (C₀ * B) * a -
    Real.log z / a + 2 * c + 16 * Real.sqrt t * dlog

/-- A source-matching seven-term numerical majorant. The six error powers
are exactly those in the paper's final table, with the trace correction
added as the seventh term. Fixed logarithms remain explicit. -/
noncomputable def finalSharpPowerEnvelope
    (Ce C₀ CB Ca Ctr Cdim lq : ℝ) (n : ℕ) : ℝ :=
  (4 * Ce + 20) * (n : ℝ) ^ (62497 / 62500 : ℝ) +
    2 * (8 * Ce + 14 + 12 * lq) * (n : ℝ) ^ (124969 / 125000 : ℝ) +
    4 * (n : ℝ) ^ (74969 / 100000 : ℝ) * (1 + Real.log (n : ℝ) / 4000) +
    (74 * Ca * C₀ * CB) * (n : ℝ) ^ (250061 / 1000000 : ℝ) *
      Real.log (n : ℝ) ^ 12 +
    2 * (n : ℝ) ^ (-4962503 / 50000 : ℝ) +
    6 * (n : ℝ) ^ (3 / 5 : ℝ) +
    (16 * Real.sqrt Ctr * (1 + Cdim)) * (n : ℝ) ^ (-248 : ℝ)

/-- The target and positive-prefix source entropy budgets have one explicit
common quadratic-near-linear majorant. Both continuity errors remain in the
hypotheses rather than being replaced by zero. -/
theorem finalSharp_source_entropy_bounds {n L : ℕ} (hn : 1 ≤ n)
    (hL : L ≤ n) {Ce St Bsh : ℝ} (hCe : 0 ≤ Ce)
    (hSt : St ≤ Ce * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) +
      (n : ℝ) ^ (-247 : ℝ))
    (hBsh : Bsh ≤ Ce * ((n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + n) +
      (n : ℝ) ^ (-247 : ℝ)) :
    St ≤ (Ce + 1) * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) ∧
      Bsh ≤ 2 * (Ce + 1) * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have he : 0 ≤ (Exponents.boxError : ℝ) := by norm_num [Exponents.boxError]
  have hsmall : (n : ℝ) ^ (-247 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hlarge : 1 ≤ (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) :=
    Real.one_le_rpow hn1 (by positivity)
  have hnlarge : (n : ℝ) ≤ (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn1 (show (1 : ℝ) ≤ 1 +
        (Exponents.boxError : ℝ) by linarith)
  have hLpower : (L : ℝ) ^ (Exponents.boxError : ℝ) ≤
      (n : ℝ) ^ (Exponents.boxError : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg L) (Nat.cast_le.mpr hL) he
  have hshell : (n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + n ≤
      2 * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hLpower hnpos.le
    rw [Real.rpow_add hnpos, Real.rpow_one]
    rw [Real.rpow_add hnpos, Real.rpow_one] at hnlarge
    linarith
  refine ⟨by nlinarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hshell hCe]

/-- The actual source budgets bound every term of the final entropy error.
The only per-band premises are the two quantitative consequences of its
literal rounded scales. All coefficients are independent of scalar data. -/
theorem finalSharpError_le_powerEnvelope
    {n L : ℕ} (hn : 2 ≤ n) (hL : L ≤ n)
    {a Ce C₀ CB Ca Ctr Cdim B St Bsh z lq t dlog : ℝ}
    (ha : 0 < a) (hCe : 0 ≤ Ce) (hC₀ : 0 ≤ C₀) (hCB : 0 ≤ CB)
    (hCa : 0 ≤ Ca) (hCtr : 0 ≤ Ctr) (hCdim : 0 ≤ Cdim) (hlq : 0 ≤ lq)
    (haUpper : a ≤ Ca * (n : ℝ) ^ (-37497 / 50000 : ℝ))
    (haInv : 1 / a ≤ (n : ℝ) ^ (37497 / 50000 : ℝ))
    (hz : 0 < z) (hzupper : z ≤ 1)
    (hmass : 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z)
    (hSt : St ≤ Ce * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) +
      (n : ℝ) ^ (-247 : ℝ))
    (hBsh : Bsh ≤ Ce * ((n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + n) +
      (n : ℝ) ^ (-247 : ℝ))
    (hB : B ≤ CB * ((n : ℝ) *
      (Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ)) : ℝ) *
        Real.log (n : ℝ) ^ 12))
    (ht : t ≤ Ctr * (n : ℝ) ^ (-500 : ℝ))
    (hdlog : dlog ≤ 1 + Cdim * (n : ℝ) ^ 2) :
    finalSharpError n a C₀ B St Bsh z lq t dlog ≤
      finalSharpPowerEnvelope Ce C₀ CB Ca Ctr Cdim lq n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  let N := (n : ℝ) ^ (1 + (Exponents.boxError : ℝ))
  let c := (n : ℝ) ^ (3 / 5 : ℝ) - Real.log z
  let D := Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ))
  let H := 4 * St + 2 * c + 2 * Bsh + 6 * (n : ℝ) * (D : ℝ) * lq
  obtain ⟨hlogz0, hlogz⟩ := finalSharp_neg_log_mass_le hn hz hzupper hmass
  obtain ⟨hStN, hBshN⟩ := finalSharp_source_entropy_bounds
    (show 1 ≤ n by omega) hL hCe hSt hBsh
  change St ≤ (Ce + 1) * N at hStN
  change Bsh ≤ 2 * (Ce + 1) * N at hBshN
  have hwN : (n : ℝ) ^ (3 / 5 : ℝ) ≤ N :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num [Exponents.boxError])
  have hsmallw : (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hc : c ≤ 3 * (n : ℝ) ^ (3 / 5 : ℝ) := by dsimp only [c]; linarith
  have hcN : c ≤ 3 * N := hc.trans (by linarith)
  have hD : (D : ℝ) ≤ 2 * (n : ℝ) ^ (Exponents.scannerKappa : ℝ) := by
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg n) (Exponents.scannerKappa : ℝ))
    have hone : 1 ≤ (n : ℝ) ^ (Exponents.scannerKappa : ℝ) :=
      Real.one_le_rpow hn1 (by norm_num [Exponents.scannerKappa])
    dsimp only [D]
    linarith
  have hnD : (n : ℝ) * (D : ℝ) ≤ 2 * N := by
    have hpow : (n : ℝ) ^ (Exponents.scannerKappa : ℝ) ≤
        (n : ℝ) ^ (Exponents.boxError : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1
        (by norm_num [Exponents.scannerKappa, Exponents.boxError])
    calc
      (n : ℝ) * (D : ℝ) ≤ (n : ℝ) * (2 * (n : ℝ) ^
          (Exponents.scannerKappa : ℝ)) :=
        mul_le_mul_of_nonneg_left hD hnpos.le
      _ ≤ (n : ℝ) * (2 * (n : ℝ) ^ (Exponents.boxError : ℝ)) := by gcongr
      _ = 2 * N := by dsimp only [N]; rw [Real.rpow_add hnpos, Real.rpow_one]; ring
  have hH : H ≤ (8 * Ce + 14 + 12 * lq) * N := by
    have hDq := mul_le_mul_of_nonneg_right hnD hlq
    dsimp only [H]
    nlinarith only [hStN, hBshN, hcN, hDq]
  have hhead : (4 * St + 4 * c - 2 * Real.log z) /
      (n : ℝ) ^ (Exponents.scannerOmega : ℝ) ≤
        (4 * Ce + 20) * (n : ℝ) ^ (62497 / 62500 : ℝ) := by
    have hnum : 4 * St + 4 * c - 2 * Real.log z ≤ (4 * Ce + 20) * N := by
      nlinarith only [hStN, hcN, hlogz, hsmallw, hwN]
    calc
      _ ≤ ((4 * Ce + 20) * N) / (n : ℝ) ^ (Exponents.scannerOmega : ℝ) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = _ := by
        dsimp only [N]
        rw [mul_div_assoc, ← Real.rpow_sub hnpos]
        norm_num [Exponents.boxError, Exponents.scannerOmega]
  have hmassCost : ((n : ℝ) ^ (-(1 / 4000 : ℝ)) +
      (n : ℝ) ^ (-(1 / 2000 : ℝ)) / (n : ℝ) ^ (-(1 / 4000 : ℝ))) * H ≤
        2 * (8 * Ce + 14 + 12 * lq) * (n : ℝ) ^ (124969 / 125000 : ℝ) := by
    have hratio : (n : ℝ) ^ (-(1 / 2000 : ℝ)) /
        (n : ℝ) ^ (-(1 / 4000 : ℝ)) = (n : ℝ) ^ (-(1 / 4000 : ℝ)) := by
      rw [← Real.rpow_sub hnpos]
      norm_num
    rw [hratio]
    calc
      _ ≤ (2 * (n : ℝ) ^ (-(1 / 4000 : ℝ))) *
          ((8 * Ce + 14 + 12 * lq) * N) := by
        simpa only [two_mul] using mul_le_mul_of_nonneg_left hH
          (show 0 ≤ 2 * (n : ℝ) ^ (-(1 / 4000 : ℝ)) by positivity)
      _ = _ := by
        dsimp only [N]
        rw [show (2 * (n : ℝ) ^ (-(1 / 4000 : ℝ))) *
          ((8 * Ce + 14 + 12 * lq) * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ))) =
            2 * (8 * Ce + 14 + 12 * lq) * ((n : ℝ) ^ (-(1 / 4000 : ℝ)) *
              (n : ℝ) ^ (1 + (Exponents.boxError : ℝ))) by ring,
          ← Real.rpow_add hnpos]
        norm_num [Exponents.boxError]
  have hbinary := finalSharp_binary_cost_le hn ha haInv
  have hBpower : B ≤ (2 * CB) * (n : ℝ) ^ (1 + (Exponents.scannerKappa : ℝ)) *
      Real.log (n : ℝ) ^ 12 := by
    calc
      B ≤ CB * ((n : ℝ) * (D : ℝ) * Real.log (n : ℝ) ^ 12) := hB
      _ ≤ CB * ((n : ℝ) * (2 * (n : ℝ) ^ (Exponents.scannerKappa : ℝ)) *
          Real.log (n : ℝ) ^ 12) := by gcongr
      _ = _ := by rw [Real.rpow_add hnpos, Real.rpow_one]; ring
  have hmoment : 37 * (C₀ * B) * a ≤
      (74 * Ca * C₀ * CB) * (n : ℝ) ^ (250061 / 1000000 : ℝ) *
        Real.log (n : ℝ) ^ 12 := by
    calc
      _ ≤ 37 * (C₀ * ((2 * CB) * (n : ℝ) ^ (1 + (Exponents.scannerKappa : ℝ)) *
          Real.log (n : ℝ) ^ 12)) * a := by gcongr
      _ ≤ 37 * (C₀ * ((2 * CB) * (n : ℝ) ^ (1 + (Exponents.scannerKappa : ℝ)) *
          Real.log (n : ℝ) ^ 12)) *
            (Ca * (n : ℝ) ^ (-37497 / 50000 : ℝ)) := by gcongr
      _ = _ := by
        rw [show 37 * (C₀ * ((2 * CB) * (n : ℝ) ^ (1 + (Exponents.scannerKappa : ℝ)) *
          Real.log (n : ℝ) ^ 12)) * (Ca * (n : ℝ) ^ (-37497 / 50000 : ℝ)) =
            (74 * Ca * C₀ * CB) *
              ((n : ℝ) ^ (1 + (Exponents.scannerKappa : ℝ)) *
                (n : ℝ) ^ (-37497 / 50000 : ℝ)) * Real.log (n : ℝ) ^ 12 by ring,
          ← Real.rpow_add hnpos]
        norm_num [Exponents.scannerKappa]
  have hmassLog : -Real.log z / a ≤ 2 * (n : ℝ) ^ (-4962503 / 50000 : ℝ) := by
    calc
      -Real.log z / a = (-Real.log z) * (1 / a) := by ring
      _ ≤ (2 * (n : ℝ) ^ (-100 : ℝ)) * (n : ℝ) ^ (37497 / 50000 : ℝ) :=
        mul_le_mul hlogz haInv (by positivity) (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hnpos]; norm_num
  have hsqrt : Real.sqrt t ≤ Real.sqrt Ctr * (n : ℝ) ^ (-250 : ℝ) := by
    calc
      Real.sqrt t ≤ Real.sqrt (Ctr * (n : ℝ) ^ (-500 : ℝ)) := Real.sqrt_le_sqrt ht
      _ = _ := by
        rw [Real.sqrt_mul hCtr, Real.sqrt_eq_rpow ((n : ℝ) ^ (-500 : ℝ)),
          ← Real.rpow_mul hnpos.le]
        norm_num
  have hdlog' : dlog ≤ (1 + Cdim) * (n : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith [one_le_pow₀ hn1 (n := 2)]
  have htrace : 16 * Real.sqrt t * dlog ≤
      (16 * Real.sqrt Ctr * (1 + Cdim)) * (n : ℝ) ^ (-248 : ℝ) := by
    calc
      _ ≤ 16 * Real.sqrt t * ((1 + Cdim) * (n : ℝ) ^ (2 : ℝ)) := by gcongr
      _ ≤ 16 * (Real.sqrt Ctr * (n : ℝ) ^ (-250 : ℝ)) *
          ((1 + Cdim) * (n : ℝ) ^ (2 : ℝ)) := by gcongr
      _ = _ := by
        rw [show 16 * (Real.sqrt Ctr * (n : ℝ) ^ (-250 : ℝ)) *
          ((1 + Cdim) * (n : ℝ) ^ (2 : ℝ)) =
            (16 * Real.sqrt Ctr * (1 + Cdim)) *
              ((n : ℝ) ^ (-250 : ℝ) * (n : ℝ) ^ (2 : ℝ)) by ring,
          ← Real.rpow_add hnpos]
        norm_num
  change (4 * St + 4 * c - 2 * Real.log z) /
      (n : ℝ) ^ (Exponents.scannerOmega : ℝ) +
    ((n : ℝ) ^ (-(1 / 4000 : ℝ)) + (n : ℝ) ^ (-(1 / 2000 : ℝ)) /
      (n : ℝ) ^ (-(1 / 4000 : ℝ))) * H +
    (3 + 1 / a) * Real.binEntropy ((n : ℝ) ^ (-(1 / 4000 : ℝ))) +
      37 * (C₀ * B) * a - Real.log z / a + 2 * c +
        16 * Real.sqrt t * dlog ≤ _
  unfold finalSharpPowerEnvelope
  linarith only [hhead, hmassCost, hbinary, hmoment, hmassLog, hc, htrace]

end TNLean.PEPS.AreaLaw.Scan
