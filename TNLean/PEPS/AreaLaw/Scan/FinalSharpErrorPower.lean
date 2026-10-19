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
remaining scalar datum. The logarithmic absorption threshold is given explicitly by
`finalSharpEnvelopeThreshold`, and the full threshold of `exists_finalSharp_error_le` is
`finalSharpErrorThreshold C₀ CB`, the maximum of `finalSharpScaleThreshold` and
`finalSharpEnvelopeThreshold C₀ CB 32`, with coefficient `finalSharpErrorConstant`. This is
conditional final-scale absorption. It does not construct the safe-box entropy input, the
scanner, or a physical mutual-information inequality. Replica remainders must first be removed
with the physical instance, size, total weight and fraction fixed.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 839--942,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
See `docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

open Filter

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
      A * (n : ℝ) ^ u * Real.log (n : ℝ) ^ Cl ≤ (n : ℝ) ^ v :=
  eventually_atTop.2 ⟨_, fun _ hn => by simpa only [one_mul] using
    Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le hA one_pos huv hn⟩

/-- The explicit threshold of the logarithmic absorption in the final error envelope: the
thresholds for `n^(74969/100000) log n / 1000 ≤ n^(62497/62500)` and
`74 C_a C₀ C_B n^(250061/1000000) (log n)^12 ≤ n^(62497/62500)`
(`08-scanner.tex`, lines 839--942). -/
noncomputable def finalSharpEnvelopeThreshold (C₀ CB Ca : ℝ) : ℕ :=
  max ⌈Real.logRpowThreshold (1 / 1000) 1 (74969 / 100000) (62497 / 62500) 1⌉₊
    ⌈Real.logRpowThreshold (74 * Ca * C₀ * CB) 1 (250061 / 1000000) (62497 / 62500) 12⌉₊

/-- The seven source errors have their exact maximum power at every `n` from the explicit
threshold `finalSharpEnvelopeThreshold C₀ CB Ca` on. The displayed coefficient is explicit
and independent of `C0`, `CB` and `Ca`; their effect enters the threshold.
Source: `08-scanner.tex`, lines 839--942. -/
theorem finalSharp_powerEnvelope_le_of_finalSharpEnvelopeThreshold_le
    {Ce C₀ CB Ca Ctr Cdim lq : ℝ}
    (hCe : 0 ≤ Ce) (hC₀ : 0 ≤ C₀) (hCB : 0 ≤ CB) (hCa : 0 ≤ Ca)
    (_hCtr : 0 ≤ Ctr) (hCdim : 0 ≤ Cdim) (hlq : 0 ≤ lq) {n : ℕ}
    (hthr : finalSharpEnvelopeThreshold C₀ CB Ca ≤ n) :
    finalSharpPowerEnvelope Ce C₀ CB Ca Ctr Cdim lq n ≤
      (20 * Ce + 62 + 24 * lq + 16 * Real.sqrt Ctr * (1 + Cdim)) *
        (n : ℝ) ^ (62497 / 62500 : ℝ) := by
  have hn : 1 ≤ n := by
    have := Real.two_le_of_ceil_logRpowThreshold_le ((le_max_left _ _).trans hthr)
    omega
  have hbin : (1 / 1000 : ℝ) * (n : ℝ) ^ (74969 / 100000 : ℝ) * Real.log (n : ℝ) ≤
      (n : ℝ) ^ (62497 / 62500 : ℝ) := by
    simpa only [Real.rpow_one, one_mul] using
      Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le (by norm_num)
        one_pos (by norm_num) ((le_max_left _ _).trans hthr)
  have hmom : (74 * Ca * C₀ * CB) * (n : ℝ) ^ (250061 / 1000000 : ℝ) *
      Real.log (n : ℝ) ^ 12 ≤ (n : ℝ) ^ (62497 / 62500 : ℝ) := by
    simpa only [Real.rpow_ofNat, one_mul] using
      Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le (by positivity)
        one_pos (by norm_num) ((le_max_right _ _).trans hthr)
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

/-- The seven source errors have their exact maximum power after absorbing
only fixed logarithmic factors. The displayed coefficient is explicit and
independent of `C0`, `CB` and `Ca`; their effect enters the threshold. -/
theorem eventually_finalSharp_powerEnvelope_le
    {Ce C₀ CB Ca Ctr Cdim lq : ℝ}
    (hCe : 0 ≤ Ce) (hC₀ : 0 ≤ C₀) (hCB : 0 ≤ CB) (hCa : 0 ≤ Ca)
    (_hCtr : 0 ≤ Ctr) (hCdim : 0 ≤ Cdim) (hlq : 0 ≤ lq) :
    ∀ᶠ n : ℕ in atTop,
      finalSharpPowerEnvelope Ce C₀ CB Ca Ctr Cdim lq n ≤
        (20 * Ce + 62 + 24 * lq + 16 * Real.sqrt Ctr * (1 + Cdim)) *
          (n : ℝ) ^ (62497 / 62500 : ℝ) :=
  eventually_atTop.2 ⟨_, fun _ => finalSharp_powerEnvelope_le_of_finalSharpEnvelopeThreshold_le
    hCe hC₀ hCB hCa _hCtr hCdim hlq⟩

/-- The explicit threshold of the final source error: the final-scale threshold and the
logarithmic absorption threshold at `C_a = 32` (`08-scanner.tex`, lines 839--942). -/
noncomputable def finalSharpErrorThreshold (C₀ CB : ℝ) : ℕ :=
  max finalSharpScaleThreshold (finalSharpEnvelopeThreshold C₀ CB 32)

/-- The final source-error threshold is at least two. -/
theorem two_le_finalSharpErrorThreshold (C₀ CB : ℝ) : 2 ≤ finalSharpErrorThreshold C₀ CB :=
  two_le_finalSharpScaleThreshold.trans (le_max_left _ _)

/-- The explicit coefficient `20 Ce + 62 + 24 lq + 16 √Ctr (1 + Cdim)` of the final source
error at the exact maximal power and at the sublinear power, where `lq` stands for `log q`
(`08-scanner.tex`, lines 839--942). -/
noncomputable def finalSharpErrorConstant (Ce Ctr Cdim lq : ℝ) : ℝ :=
  20 * Ce + 62 + 24 * lq + 16 * Real.sqrt Ctr * (1 + Cdim)

/-- The final source-error coefficient is positive. -/
theorem finalSharpErrorConstant_pos {Ce Ctr Cdim lq : ℝ} (hCe : 0 ≤ Ce) (hCdim : 0 ≤ Cdim)
    (hlq : 0 ≤ lq) : 0 < finalSharpErrorConstant Ce Ctr Cdim lq := by
  unfold finalSharpErrorConstant; positivity

/-- The complete source error is bounded at the exact maximal power and at the paper's
sublinear power with the explicit coefficient `finalSharpErrorConstant Ce Ctr Cdim lq`, at every
`n` from the explicit threshold `finalSharpErrorThreshold C₀ CB` on. The target and prefix
entropy antecedents are explicit. Every floor, division and ceiling is literal.
Source: `08-scanner.tex`, lines 839--942. -/
theorem finalSharp_error_le_of_finalSharpErrorThreshold_le
    (Ce C₀ CB Ctr Cdim lq : ℝ)
    (hCe : 0 ≤ Ce) (hC₀ : 0 ≤ C₀) (hCB : 0 ≤ CB)
    (hCtr : 0 ≤ Ctr) (hCdim : 0 ≤ Cdim) (hlq : 0 ≤ lq) {n : ℕ}
    (hn : finalSharpErrorThreshold C₀ CB ≤ n) :
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
          finalSharpErrorConstant Ce Ctr Cdim lq * (n : ℝ) ^ (62497 / 62500 : ℝ) ∧
        finalSharpError n a C₀ B St Bsh z lq t dlog ≤
          finalSharpErrorConstant Ce Ctr Cdim lq *
            (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  let Ns := finalSharpScaleThreshold
  let Ne := finalSharpEnvelopeThreshold C₀ CB 32
  have hC := finalSharpErrorConstant_pos (Ctr := Ctr) hCe hCdim hlq
  have hNs : 2 ≤ Ns := two_le_finalSharpScaleThreshold
  have hCa : (1 : ℝ) ≤ 32 := by norm_num
  intro L m K D W a
  have hn2 : 2 ≤ n := hNs.trans ((le_max_left Ns Ne).trans hn)
  obtain ⟨hK, ha, haUpper, haInv, htpos, hthalf⟩ :=
    finalSharp_scale_bounds_of_finalSharpScaleThreshold_le ((le_max_left Ns Ne).trans hn)
  refine ⟨hK, ha, htpos, hthalf, ?_⟩
  intro B St Bsh z t dlog hz hzupper hmass hSt hBsh hB ht hdlog
  have hL : L ≤ n := Nat.floor_le_of_le (by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1
      (show 1 - (Exponents.scannerEll : ℝ) ≤ 1 by norm_num [Exponents.scannerEll]))
  have hbound := (finalSharpError_le_powerEnvelope hn2 hL ha hCe hC₀ hCB
    (zero_le_one.trans hCa) hCtr hCdim hlq haUpper haInv hz hzupper hmass
    hSt hBsh hB ht hdlog).trans (finalSharp_powerEnvelope_le_of_finalSharpEnvelopeThreshold_le
      hCe hC₀ hCB (zero_le_one.trans hCa) hCtr hCdim hlq ((le_max_right Ns Ne).trans hn))
  refine ⟨hbound, hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ n by omega))
      (by norm_num [Exponents.amplificationEpsilon] :
        (62497 / 62500 : ℝ) ≤ 1 - (Exponents.amplificationEpsilon : ℝ))) hC.le

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
          C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) :=
  ⟨_, finalSharpErrorConstant_pos hCe hCdim hlq, _, two_le_finalSharpErrorThreshold C₀ CB,
    fun _ hn => finalSharp_error_le_of_finalSharpErrorThreshold_le Ce C₀ CB Ctr Cdim lq hCe hC₀
      hCB hCtr hCdim hlq hn⟩

/-- The exact source trace-distance budget may be used directly, with the explicit coefficient
`finalSharpErrorConstant Ce √(2 / g) (Cvol log q) (log q)` at every `n` from the explicit
threshold `finalSharpErrorThreshold C₀ CB` on. The fixed local dimension and target-volume
constant enter only the coefficient; the far subsystem's dimension never appears.
Source: `08-scanner.tex`, lines 839--942. -/
theorem finalSharp_source_error_le_of_finalSharpErrorThreshold_le
    (q : ℕ) (hq : 1 ≤ q) (Ce C₀ CB g Cvol : ℝ)
    (hCe : 0 ≤ Ce) (hC₀ : 0 ≤ C₀) (hCB : 0 ≤ CB)
    (hg : 0 < g) (hCvol : 0 ≤ Cvol) {n : ℕ}
    (hn : finalSharpErrorThreshold C₀ CB ≤ n) :
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
          finalSharpErrorConstant Ce (Real.sqrt (2 / g)) (Cvol * Real.log q) (Real.log q) *
            (n : ℝ) ^ (62497 / 62500 : ℝ) ∧
        finalSharpError n a C₀ B St Bsh z (Real.log q) t dlog ≤
          finalSharpErrorConstant Ce (Real.sqrt (2 / g)) (Cvol * Real.log q) (Real.log q) *
            (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  intro L m K D W a
  obtain ⟨hK, ha, htpos, hthalf, hb⟩ :=
    finalSharp_error_le_of_finalSharpErrorThreshold_le Ce C₀ CB (Real.sqrt (2 / g))
      (Cvol * Real.log q) (Real.log q) hCe hC₀ hCB (Real.sqrt_nonneg _)
      (mul_nonneg hCvol hlq) hlq hn
  refine ⟨hK, ha, htpos, hthalf, ?_⟩
  intro B St Bsh z t dlog hz hzupper hmass hSt hBsh hB ht hdlog
  exact hb B St Bsh z t dlog hz hzupper hmass hSt hBsh hB
    (finalSharp_traceDistance_power hg ht) hdlog

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
          C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) :=
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  ⟨_, finalSharpErrorConstant_pos hCe (mul_nonneg hCvol hlq) hlq, _,
    two_le_finalSharpErrorThreshold C₀ CB, fun _ hn =>
      finalSharp_source_error_le_of_finalSharpErrorThreshold_le q hq Ce C₀ CB g Cvol hCe hC₀
        hCB hg hCvol hn⟩

end TNLean.PEPS.AreaLaw.Scan
