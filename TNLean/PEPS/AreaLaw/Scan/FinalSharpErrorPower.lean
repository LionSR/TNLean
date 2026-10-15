/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FinalSharpErrorBudget

/-!
# Final source error absorption with the paper's exponent

With the source entropy antecedent at `boxError = 2 / 1000000`, the largest
error power is exactly `62497/62500 = 0.999952`. The two logarithmic costs
are absorbed at that power. Its margin to the claimed collar power
`1 - 1/100000 = 0.99999` is exactly `19/500000`.

All coefficients are fixed before the size threshold, which precedes every
remaining scalar datum. This is conditional final-scale absorption. It does
not construct the safe-box entropy input, the scanner, or a physical
mutual-information inequality. Replica remainders must first be removed
with the physical instance, size, total weight and fraction fixed.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 839--942,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
See `docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

open Filter Asymptotics

namespace TNLean.PEPS.AreaLaw.Scan

/-- The exact source error powers, their maximum, and its strict margin to
the final collar exponent. The constants are rational equalities. -/
theorem finalSharp_error_exponents :
    1 + (Exponents.boxError : ℝ) - (Exponents.scannerOmega : ℝ) =
        (62497 / 62500 : ℝ) ∧
    1 + (Exponents.boxError : ℝ) - 1 / 4000 = (124969 / 125000 : ℝ) ∧
    1 - (Exponents.scannerEll : ℝ) - (Exponents.scannerMu : ℝ) -
        (Exponents.scannerOmega : ℝ) - 1 / 4000 = (74969 / 100000 : ℝ) ∧
    (Exponents.scannerOmega : ℝ) - (1 - (Exponents.scannerEll : ℝ) -
        (Exponents.scannerMu : ℝ)) + 1 + (Exponents.scannerKappa : ℝ) =
      (250061 / 1000000 : ℝ) ∧
    -100 + (1 - (Exponents.scannerEll : ℝ) - (Exponents.scannerMu : ℝ)) -
        (Exponents.scannerOmega : ℝ) = (-4962503 / 50000 : ℝ) ∧
    max (62497 / 62500 : ℝ)
      (max (3 / 5 : ℝ) (max (124969 / 125000 : ℝ)
        (max (74969 / 100000 : ℝ)
          (max (250061 / 1000000 : ℝ) (max (-4962503 / 50000 : ℝ) (-248)))))) =
        (62497 / 62500 : ℝ) ∧
    (1 - (Exponents.amplificationEpsilon : ℝ)) - (62497 / 62500 : ℝ) =
      (19 / 500000 : ℝ) := by
  norm_num [Exponents.boxError, Exponents.scannerOmega, Exponents.scannerEll,
    Exponents.scannerMu, Exponents.scannerKappa, Exponents.amplificationEpsilon]

/-- A fixed logarithmic cost is absorbed by any strict power margin.
This helper is independent of the physical comparison and replica count. -/
theorem eventually_finalSharp_log_cost_le (A Cl u v : ℝ)
    (hA : 0 ≤ A) (huv : u < v) :
    ∀ᶠ n : ℕ in atTop,
      A * (n : ℝ) ^ u * Real.log (n : ℝ) ^ Cl ≤ (n : ℝ) ^ v := by
  have hlog : (fun n : ℕ => A * Real.log (n : ℝ) ^ Cl) =o[atTop]
      fun n => (n : ℝ) ^ (v - u) :=
    (isLittleO_log_rpow_rpow_atTop Cl (sub_pos.mpr huv)).natCast_atTop.const_mul_left A
  filter_upwards [eventually_ge_atTop 2, hlog.bound (by norm_num : (0 : ℝ) < 1)]
    with n hn hsmall
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hsmall' : A * Real.log (n : ℝ) ^ Cl ≤ (n : ℝ) ^ (v - u) := by
    simpa only [Real.norm_of_nonneg (mul_nonneg hA (Real.rpow_nonneg hlog0 Cl)),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (v - u)), one_mul]
      using hsmall
  calc
    _ = (A * Real.log (n : ℝ) ^ Cl) * (n : ℝ) ^ u := by ring
    _ ≤ (n : ℝ) ^ (v - u) * (n : ℝ) ^ u :=
      mul_le_mul_of_nonneg_right hsmall' (by positivity)
    _ = _ := by rw [← Real.rpow_add hnpos, sub_add_cancel]

/-- The seven source errors have their exact maximum power after absorbing
only fixed logarithmic factors. The displayed coefficient is explicit and
independent of `C0`, `CB` and `Ca`; their effect enters the threshold. -/
theorem eventually_finalSharp_powerEnvelope_le
    {Ce C₀ CB Ca Ctr Cdim lq : ℝ}
    (hCe : 0 ≤ Ce) (hC₀ : 0 ≤ C₀) (hCB : 0 ≤ CB) (hCa : 0 ≤ Ca)
    (hCtr : 0 ≤ Ctr) (hCdim : 0 ≤ Cdim) (hlq : 0 ≤ lq) :
    ∀ᶠ n : ℕ in atTop,
      finalSharpPowerEnvelope Ce C₀ CB Ca Ctr Cdim lq n ≤
        (20 * Ce + 62 + 24 * lq + 16 * Real.sqrt Ctr * (1 + Cdim)) *
          (n : ℝ) ^ (62497 / 62500 : ℝ) := by
  have hbinary : ∀ᶠ n : ℕ in atTop,
      (1 / 1000 : ℝ) * (n : ℝ) ^ (74969 / 100000 : ℝ) * Real.log (n : ℝ) ≤
        (n : ℝ) ^ (62497 / 62500 : ℝ) := by
    simpa only [Real.rpow_one] using
      eventually_finalSharp_log_cost_le (1 / 1000) 1
        (74969 / 100000) (62497 / 62500) (by norm_num) (by norm_num)
  have hmoment : ∀ᶠ n : ℕ in atTop,
      (74 * Ca * C₀ * CB) * (n : ℝ) ^ (250061 / 1000000 : ℝ) *
        Real.log (n : ℝ) ^ 12 ≤ (n : ℝ) ^ (62497 / 62500 : ℝ) := by
    simpa only [Real.rpow_ofNat] using
      eventually_finalSharp_log_cost_le (74 * Ca * C₀ * CB) 12
        (250061 / 1000000) (62497 / 62500) (by positivity) (by norm_num)
  filter_upwards [eventually_ge_atTop 1, hbinary, hmoment] with n hn hbin hmom
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmono (u : ℝ) (hu : u ≤ (62497 / 62500 : ℝ)) :
      (n : ℝ) ^ u ≤ (n : ℝ) ^ (62497 / 62500 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hu
  have hmass := mul_le_mul_of_nonneg_left
    (hmono (124969 / 125000) (by norm_num))
    (show 0 ≤ 2 * (8 * Ce + 14 + 12 * lq) by positivity)
  have hbin0 := mul_le_mul_of_nonneg_left
    (hmono (74969 / 100000) (by norm_num)) (by norm_num : (0 : ℝ) ≤ 4)
  have hbin' : 4 * (n : ℝ) ^ (74969 / 100000 : ℝ) *
      (1 + Real.log (n : ℝ) / 4000) ≤
        5 * (n : ℝ) ^ (62497 / 62500 : ℝ) := by nlinarith only [hbin, hbin0]
  have hz := mul_le_mul_of_nonneg_left
    (hmono (-4962503 / 50000) (by norm_num)) (by norm_num : (0 : ℝ) ≤ 2)
  have hw := mul_le_mul_of_nonneg_left
    (hmono (3 / 5) (by norm_num)) (by norm_num : (0 : ℝ) ≤ 6)
  have ht := mul_le_mul_of_nonneg_left
    (hmono (-248) (by norm_num))
    (show 0 ≤ 16 * Real.sqrt Ctr * (1 + Cdim) by positivity)
  unfold finalSharpPowerEnvelope
  nlinarith only [hmass, hbin', hmom, hz, hw, ht]

/-- One threshold bounds the complete source error at the exact maximal
power and at the paper's sublinear power. The target and prefix entropy
antecedents are explicit. Every floor, division and ceiling is literal. -/
theorem exists_finalSharp_error_le
    (Ce C₀ CB Ctr Cdim lq : ℝ)
    (hCe : 0 ≤ Ce) (hC₀ : 0 ≤ C₀) (hCB : 0 ≤ CB)
    (hCtr : 0 ≤ Ctr) (hCdim : 0 ≤ Cdim) (hlq : 0 ≤ lq) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
      let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
      let K := L / (8 * m)
      let D := Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ))
      let W := (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
      let a := W / (K : ℝ)
      1 ≤ K ∧ 0 < a ∧
        0 < (n : ℝ) ^ (-(1 / 4000 : ℝ)) ∧
        (n : ℝ) ^ (-(1 / 4000 : ℝ)) ≤ 1 / 2 ∧
      ∀ B St Bsh z t dlog : ℝ,
        0 < z → z ≤ 1 → 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z →
        St ≤ Ce * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) +
          (n : ℝ) ^ (-247 : ℝ) →
        Bsh ≤ Ce * ((n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + n) +
          (n : ℝ) ^ (-247 : ℝ) →
        B ≤ CB * ((n : ℝ) * (D : ℝ) * Real.log (n : ℝ) ^ 12) →
        t ≤ Ctr * (n : ℝ) ^ (-500 : ℝ) →
        dlog ≤ 1 + Cdim * (n : ℝ) ^ 2 →
        finalSharpError n a C₀ B St Bsh z lq t dlog ≤
          C * (n : ℝ) ^ (62497 / 62500 : ℝ) ∧
        finalSharpError n a C₀ B St Bsh z lq t dlog ≤
          C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  obtain ⟨Ca, hCa, Ns, hNs, hscale⟩ := exists_finalSharp_scale_bounds
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp
    (eventually_finalSharp_powerEnvelope_le hCe hC₀ hCB
      (zero_le_one.trans hCa) hCtr hCdim hlq)
  let C := 20 * Ce + 62 + 24 * lq + 16 * Real.sqrt Ctr * (1 + Cdim)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, max Ns Ne, hNs.trans (le_max_left _ _), ?_⟩
  intro n hn L m K D W a
  have hn2 : 2 ≤ n := hNs.trans ((le_max_left Ns Ne).trans hn)
  obtain ⟨hK, ha, haUpper, haInv, htpos, hthalf⟩ :=
    hscale n ((le_max_left Ns Ne).trans hn)
  refine ⟨hK, ha, htpos, hthalf, ?_⟩
  intro B St Bsh z t dlog hz hzupper hmass hSt hBsh hB ht hdlog
  have hL : L ≤ n := Nat.floor_le_of_le (by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1
      (show 1 - (Exponents.scannerEll : ℝ) ≤ 1 by norm_num [Exponents.scannerEll]))
  have hbound := (finalSharpError_le_powerEnvelope hn2 hL ha hCe hC₀ hCB
    (zero_le_one.trans hCa) hCtr hCdim hlq haUpper haInv hz hzupper hmass
    hSt hBsh hB ht hdlog).trans (hNe n ((le_max_right Ns Ne).trans hn))
  refine ⟨hbound, hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ n by omega))
      (by norm_num [Exponents.amplificationEpsilon] :
        (62497 / 62500 : ℝ) ≤ 1 - (Exponents.amplificationEpsilon : ℝ))) hC.le

/-- The exact source trace-distance budget may be used directly. The fixed
local dimension and target-volume constant precede the threshold; the far
subsystem's dimension never appears. The two entropy antecedents still
require the preceding source safe-box input. -/
theorem exists_finalSharp_source_error_le
    (q : ℕ) (hq : 1 ≤ q) (Ce C₀ CB g Cvol : ℝ)
    (hCe : 0 ≤ Ce) (hC₀ : 0 ≤ C₀) (hCB : 0 ≤ CB)
    (hg : 0 < g) (hCvol : 0 ≤ Cvol) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
      let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
      let K := L / (8 * m)
      let D := Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ))
      let W := (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
      let a := W / (K : ℝ)
      1 ≤ K ∧ 0 < a ∧
        0 < (n : ℝ) ^ (-(1 / 4000 : ℝ)) ∧
        (n : ℝ) ^ (-(1 / 4000 : ℝ)) ≤ 1 / 2 ∧
      ∀ B St Bsh z t dlog : ℝ,
        0 < z → z ≤ 1 → 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z →
        St ≤ Ce * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) +
          (n : ℝ) ^ (-247 : ℝ) →
        Bsh ≤ Ce * ((n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + n) +
          (n : ℝ) ^ (-247 : ℝ) →
        B ≤ CB * ((n : ℝ) * (D : ℝ) * Real.log (n : ℝ) ^ 12) →
        t ≤ Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) →
        dlog ≤ 1 + (Cvol * Real.log q) * (n : ℝ) ^ 2 →
        finalSharpError n a C₀ B St Bsh z (Real.log q) t dlog ≤
          C * (n : ℝ) ^ (62497 / 62500 : ℝ) ∧
        finalSharpError n a C₀ B St Bsh z (Real.log q) t dlog ≤
          C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  obtain ⟨C, hC, N, hN, hbound⟩ :=
    exists_finalSharp_error_le Ce C₀ CB (Real.sqrt (2 / g))
      (Cvol * Real.log q) (Real.log q) hCe hC₀ hCB
      (Real.sqrt_nonneg _) (mul_nonneg hCvol hlq) hlq
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn L m K D W a
  obtain ⟨hK, ha, htpos, hthalf, hb⟩ := hbound n hn
  refine ⟨hK, ha, htpos, hthalf, ?_⟩
  intro B St Bsh z t dlog hz hzupper hmass hSt hBsh hB ht hdlog
  exact hb B St Bsh z t dlog hz hzupper hmass hSt hBsh hB
    (finalSharp_traceDistance_power hg ht) hdlog

end TNLean.PEPS.AreaLaw.Scan
