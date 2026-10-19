/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalBoxBootstrap
import TNLean.PEPS.AreaLaw.Scan.BootstrapIterateBound

/-!
# A power bound for one physical bootstrap round

One round of the physical safe-box bootstrap sends the current constant `C` to
`576 C_out(C) + N(C)² log q + 1 + log q` (`eq:round` of the explicit-constant note).
Here `C_out(C)` is linear in `C`. Of the entries of the round threshold `N(C)`, only the
principal energy entry depends on `C`, through `⌈(2 C_δ)^(1/ν)⌉` with `C_δ` linear in `C`.
So one round is at most `A (1 + C)^(2k)` with `k = ⌈1/ν⌉`, and `A` explicit in the round data.
With `boxBootstrapConstant_le_pow_pow` this bounds the safe-box constant after any number
`M` of rounds at least the round count by `((A + 1)(1 + C₀))^((4k)^M)`.

This is an auxiliary result: the source fixes the number of rounds but does not bound the
constants they produce.

## Main results

* `boxBootstrapStep_le_boxStepPrefactor`: one physical round is at most
  `boxStepPrefactor (1 + C)^(2 boxStepExponent e₀)`.
* `physicalBoxBootstrapConstant_le_pow_pow`, `physicalBoxConstantExplicit_le_pow_pow`: the
  safe-box constant of Proposition 9.5 after the round count is at most
  `((boxStepPrefactor + 1)(1 + C₀))^((4 boxStepExponent e₀)^M)` for every `M` at least the
  round count.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, proof of Proposition 9.5, `prop:small-box`,
`08-scanner.tex`, lines 681–805; the recursion is `eq:round` of
`docs/notes/arealaw2d_explicit_constant.tex`.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The exponent `k = ⌈1/ν⌉` of one bootstrap round, where `ν = (1 - e₀)/2000` is the error
exponent of the scanner parameters. -/
noncomputable def boxStepExponent (e₀ : ℝ) : ℕ :=
  ⌈1 / BootstrapParameters.nu e₀⌉₊

/-- The error exponent `ν = (1 - e₀)/2000` of the scanner parameters is positive for
`e₀ < 1`. -/
theorem nu_pos_of_lt_one {e₀ : ℝ} (he₀₁ : e₀ < 1) : 0 < BootstrapParameters.nu e₀ :=
  div_pos (div_pos (by linarith) two_pos) (by norm_num)

/-- The round exponent is at least one. -/
theorem one_le_boxStepExponent {e₀ : ℝ} (he₀₁ : e₀ < 1) : 1 ≤ boxStepExponent e₀ := by
  unfold boxStepExponent
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (one_div_pos.mpr (nu_pos_of_lt_one he₀₁))).ne'

/-- The natural power threshold `⌈max 1 (b^(1/ν))⌉` is at most `z^⌈1/ν⌉ + 1` whenever
`b ≤ z` and `1 ≤ z`. -/
theorem natRpowThreshold_le_pow_add_one {ν b z : ℝ} (hν : 0 < ν) (hz : 1 ≤ z) (hb : b ≤ z) :
    (Real.natRpowThreshold ν b : ℝ) ≤ z ^ ⌈1 / ν⌉₊ + 1 := by
  unfold Real.natRpowThreshold Real.powerRatioThreshold
  have hx : max 1 ((max b 0 / 1) ^ (1 / ν)) ≤ z ^ ⌈1 / ν⌉₊ := by
    rw [div_one]
    refine max_le (one_le_pow₀ hz) ?_
    calc max b 0 ^ (1 / ν) ≤ z ^ (1 / ν) :=
          Real.rpow_le_rpow (le_max_right _ _) (max_le hb (by linarith)) (one_div_pos.mpr hν).le
      _ ≤ z ^ ((⌈1 / ν⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hz (Nat.le_ceil _)
      _ = z ^ ⌈1 / ν⌉₊ := Real.rpow_natCast _ _
  have := Nat.ceil_lt_add_one (zero_le_one.trans (le_max_left 1 ((max b 0 / 1) ^ (1 / ν))))
  linarith

/-- The transport logarithmic coefficient is nonnegative. -/
theorem transportLogCoefficient_nonneg {q : ℕ} (hq : 1 ≤ q) (Cr Cent eent Cen een : ℝ) :
    0 ≤ transportLogCoefficient q Cr Cent eent Cen een := by
  unfold transportLogCoefficient
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hbase : 0 ≤ 1 + (2 * Cr + 3) ^ 2 * Real.log q :=
    add_nonneg zero_le_one (mul_nonneg (sq_nonneg _) hlq)
  have := mul_nonneg (add_nonneg (abs_nonneg Cent) (abs_nonneg Cen))
    (Real.rpow_nonneg hbase (max 0 (max eent een)))
  linarith

/-- The rectangle input coefficient is linear in the safe-box constant. -/
theorem weakRectangleSourceEntropyCoefficient_eq_mul (b Cbox : ℝ) :
    weakRectangleSourceEntropyCoefficient b Cbox =
      Cbox * weakRectangleSourceEntropyCoefficient b 1 := by
  unfold weakRectangleSourceEntropyCoefficient
  ring

/-- The scale `α` of the principal energy entry of one round: `128 + 2 C_δ(1)`, where
`C_δ(C) = roughSelectedDensityCoefficient q C_e C₁ C_t` at the rectangle input coefficient
`C_e` of the safe-box constant `C`, the charge constant `C₁ = 3 · 2^(2R(R+1))` and the
transport logarithmic coefficient `C_t`. -/
noncomputable def boxStepScale (q R : ℕ) (Ctr Cent eent Cen een : ℝ) : ℝ :=
  128 + 2 * roughSelectedDensityCoefficient q
    (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) 1)
    (3 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ))
    (transportLogCoefficient q Ctr Cent eent Cen een)

/-- The argument of the principal energy threshold of one round grows at most linearly in the
safe-box constant: it is at most `boxStepScale (1 + C)`. -/
theorem max_two_mul_roughSelectedDensityCoefficient_le {q : ℕ} (hq : 1 ≤ q) (R : ℕ)
    (Ctr Cent eent Cen een : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    max (4 * 32) (2 * roughSelectedDensityCoefficient q
        (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) C)
        (3 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ))
        (transportLogCoefficient q Ctr Cent eent Cen een)) ≤
      boxStepScale q R Ctr Cent eent Cen een * (1 + C) := by
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have ht := transportLogCoefficient_nonneg hq Ctr Cent eent Cen een
  have hw := weakRectangleSourceEntropyCoefficient_nonneg
    (by norm_num [Exponents.boxError] : (0 : ℝ) < Exponents.boxError) zero_le_one
  have hm : (0 : ℝ) ≤ 3 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) := by positivity
  unfold boxStepScale roughSelectedDensityCoefficient
  rw [weakRectangleSourceEntropyCoefficient_eq_mul _ C]
  have hP : 0 ≤ (3 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) + 1) *
      (6 * weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) 1 + 13 +
        6 * Real.log q + 2 * transportLogCoefficient q Ctr Cent eent Cen een) :=
    mul_nonneg (by linarith) (by linarith)
  have hD : 0 ≤ (3 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) + 1) *
      (6 * weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) 1 +
        C * (13 + 6 * Real.log q + 2 * transportLogCoefficient q Ctr Cent eent Cen een)) :=
    mul_nonneg (by linarith) (add_nonneg (by linarith) (mul_nonneg hC (by linarith)))
  exact max_le (by nlinarith [mul_nonneg hP hC]) (by nlinarith [mul_nonneg hP hC])

/-- The threshold of one round exceeds its value at the safe-box constant `0` by at most the
principal energy entry, the only entry that depends on the safe-box constant. -/
theorem boxImprovementThreshold_le_add (q R : ℕ) {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (J Δ Ctr ct Cent eent Cen een Cbox : ℝ) :
    boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een Cbox ≤
      boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een 0 +
        Real.natRpowThreshold (BootstrapParameters.nu e₀)
          (max (4 * 32) (2 * roughSelectedDensityCoefficient q
            (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) Cbox)
            (3 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ))
            (transportLogCoefficient q Ctr Cent eent Cen een))) := by
  simp only [boxImprovementThreshold, CollarScan.sourceBootstrapEntropyThreshold,
    bootstrapPrincipalEnergyThreshold]
  omega

/-- The restored rough-budget coefficient of one round grows at most linearly in the safe-box
constant. -/
theorem bootstrapRestoredBudgetCoefficient_weak_le {q : ℕ} (hq : 1 ≤ q) {C : ℝ} (hC : 0 ≤ C) :
    bootstrapRestoredBudgetCoefficient q
        (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) C) ≤
      bootstrapRestoredBudgetCoefficient q
          (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) 1) * (1 + C) := by
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hw := weakRectangleSourceEntropyCoefficient_nonneg
    (by norm_num [Exponents.boxError] : (0 : ℝ) < Exponents.boxError) zero_le_one
  have hc : 0 ≤ 5 + Real.log 2 / 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  unfold bootstrapRestoredBudgetCoefficient bootstrapRestoredBudgetBaseCoefficient
  rw [weakRectangleSourceEntropyCoefficient_eq_mul _ C]
  have hD : 0 ≤ (5 + Real.log 2 / 4) *
      (8 * weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) 1 +
        C * (12 * Real.log q + 30)) :=
    mul_nonneg hc (add_nonneg (by linarith) (mul_nonneg hC (by linarith)))
  nlinarith

/-- The restored rough-budget coefficient at the safe-box constant `1` is nonnegative. -/
theorem bootstrapRestoredBudgetCoefficient_weak_one_nonneg {q : ℕ} (hq : 1 ≤ q) :
    0 ≤ bootstrapRestoredBudgetCoefficient q
      (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) 1) := by
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hw := weakRectangleSourceEntropyCoefficient_nonneg
    (by norm_num [Exponents.boxError] : (0 : ℝ) < Exponents.boxError) zero_le_one
  have hc : 0 ≤ 5 + Real.log 2 / 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  unfold bootstrapRestoredBudgetCoefficient bootstrapRestoredBudgetBaseCoefficient
  exact mul_nonneg (by linarith) hc

/-- The prefactor `A` of one physical bootstrap round:
`576 C_out(1) + (N(0) + 2)² α^(2k) log q + 1 + log q`, where `C_out(1)` is the restored
rough-budget coefficient at the safe-box constant `1`, `N(0)` is the round threshold at the
safe-box constant `0`, `α = boxStepScale` and `k = boxStepExponent e₀`. -/
noncomputable def boxStepPrefactor (q R : ℕ) {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (J Δ Ctr ct Cent eent Cen een : ℝ) : ℝ :=
  576 * bootstrapRestoredBudgetCoefficient q
      (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) 1) +
    ((boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een 0 : ℝ) + 2) ^ 2 *
      boxStepScale q R Ctr Cent eent Cen een ^ (2 * boxStepExponent e₀) * Real.log q +
    1 + Real.log q

/-- The scale of one round is at least `128`. -/
theorem le_boxStepScale {q : ℕ} (hq : 1 ≤ q) (R : ℕ) (Ctr Cent eent Cen een : ℝ) :
    128 ≤ boxStepScale q R Ctr Cent eent Cen een := by
  have := (le_max_left _ _).trans
    (max_two_mul_roughSelectedDensityCoefficient_le hq R Ctr Cent eent Cen een le_rfl)
  norm_num at this
  linarith

/-- The prefactor of one round is at least one. -/
theorem one_le_boxStepPrefactor {q : ℕ} (hq : 1 ≤ q) (R : ℕ) {e₀ : ℝ} (he₀ : 0 < e₀)
    (he₀₁ : e₀ < 1) (J Δ Ctr ct Cent eent Cen een : ℝ) :
    1 ≤ boxStepPrefactor q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een := by
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hβ := bootstrapRestoredBudgetCoefficient_weak_one_nonneg hq
  have hα : 0 ≤ boxStepScale q R Ctr Cent eent Cen een := by
    linarith [le_boxStepScale hq R Ctr Cent eent Cen een]
  have h2 : 0 ≤ ((boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een 0 : ℝ) +
      2) ^ 2 * boxStepScale q R Ctr Cent eent Cen een ^ (2 * boxStepExponent e₀) * Real.log q :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hα _)) hlq
  unfold boxStepPrefactor
  linarith

/-- **One physical bootstrap round is at most a power.** For `q ≥ 1` and every safe-box
constant `C ≥ 0`, one round of the physical bootstrap recursion sends `C` to at most
`boxStepPrefactor (1 + C)^(2 boxStepExponent e₀)`. Source: the recursion `eq:round` of
`docs/notes/arealaw2d_explicit_constant.tex`, from the proof of Proposition 9.5,
`08-scanner.tex`, lines 693–803. -/
theorem boxBootstrapStep_le_boxStepPrefactor {q : ℕ} (hq : 1 ≤ q) (R : ℕ) {e₀ : ℝ}
    (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) (J Δ Ctr ct Cent eent Cen een : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    boxBootstrapStep (Real.log q)
        (boxImprovementConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een) (fun _ ↦ 1) C ≤
      boxStepPrefactor q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een *
        (1 + C) ^ (2 * boxStepExponent e₀) := by
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hk := one_le_boxStepExponent he₀₁
  have hscale := max_two_mul_roughSelectedDensityCoefficient_le hq R Ctr Cent eent Cen een hC
  have hz : 1 ≤ boxStepScale q R Ctr Cent eent Cen een * (1 + C) :=
    le_trans (by norm_num) ((le_max_left _ _).trans hscale)
  have hT := natRpowThreshold_le_pow_add_one (nu_pos_of_lt_one he₀₁) hz hscale
  have hN : (boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C : ℝ) ≤
      (boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een 0 : ℝ) +
        Real.natRpowThreshold (BootstrapParameters.nu e₀)
          (max (4 * 32) (2 * roughSelectedDensityCoefficient q
            (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) C)
            (3 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ))
            (transportLogCoefficient q Ctr Cent eent Cen een))) := by
    exact_mod_cast boxImprovementThreshold_le_add q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C
  have hy : 1 ≤ (boxStepScale q R Ctr Cent eent Cen een * (1 + C)) ^ boxStepExponent e₀ :=
    one_le_pow₀ hz
  have hN0 : (0 : ℝ) ≤ boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een 0 :=
    Nat.cast_nonneg _
  have hN' : (boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C : ℝ) ≤
      ((boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een 0 : ℝ) + 2) *
        (boxStepScale q R Ctr Cent eent Cen een * (1 + C)) ^ boxStepExponent e₀ := by
    unfold boxStepExponent at hy ⊢
    nlinarith
  have hN2 : (boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C : ℝ) ^ 2 ≤
      ((boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een 0 : ℝ) + 2) ^ 2 *
        boxStepScale q R Ctr Cent eent Cen een ^ (2 * boxStepExponent e₀) *
          (1 + C) ^ (2 * boxStepExponent e₀) := by
    calc _ ≤ (((boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een 0 : ℝ) + 2) *
          (boxStepScale q R Ctr Cent eent Cen een * (1 + C)) ^ boxStepExponent e₀) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hN' 2
      _ = _ := by rw [mul_pow, ← pow_mul, mul_comm (boxStepExponent e₀) 2, mul_pow, mul_assoc]
  have h1C : 1 ≤ 1 + C := by linarith
  have hp : 1 + C ≤ (1 + C) ^ (2 * boxStepExponent e₀) := le_self_pow₀ h1C (by omega)
  have hp1 : 1 ≤ (1 + C) ^ (2 * boxStepExponent e₀) := one_le_pow₀ h1C
  have hβ := bootstrapRestoredBudgetCoefficient_weak_one_nonneg hq
  have e₁ : 576 * bootstrapRestoredBudgetCoefficient q
        (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) C) ≤
      576 * bootstrapRestoredBudgetCoefficient q
        (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) 1) *
          (1 + C) ^ (2 * boxStepExponent e₀) := by
    have := bootstrapRestoredBudgetCoefficient_weak_le hq hC
    nlinarith [mul_le_mul_of_nonneg_left hp hβ]
  have e₂ := mul_le_mul_of_nonneg_right hN2 hlq
  have e₃ : Real.log q ≤ Real.log q * (1 + C) ^ (2 * boxStepExponent e₀) :=
    le_mul_of_one_le_right hlq hp1
  simp only [boxBootstrapStep, boxImprovementConstant, boxStepPrefactor, Nat.cast_one, one_pow,
    mul_one]
  nlinarith

/-- **A closed-form bound for the physical safe-box constant.** For `q ≥ 1`, an initial
constant `C₀ ≥ 0` and every `M` at least the round count `boxBootstrapRounds e₀ e_* ℓ`, the
safe-box constant `physicalBoxBootstrapConstant` of Proposition 9.5 is at most
`((A + 1)(1 + C₀))^((4k)^M)` with `A = boxStepPrefactor` and `k = boxStepExponent e₀`.
Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–803. -/
theorem physicalBoxBootstrapConstant_le_pow_pow {q : ℕ} (hq : 1 ≤ q) (R : ℕ) {e₀ : ℝ}
    (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) (J Δ Ctr ct Cent eent Cen een : ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    {M : ℕ}
    (hM : boxBootstrapRounds e₀ (Exponents.boxError : ℝ) (BootstrapParameters.ell e₀) ≤ M) :
    physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀ ≤
      ((boxStepPrefactor q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een + 1) * (1 + C₀)) ^
        ((2 * (2 * boxStepExponent e₀)) ^ M) :=
  boxBootstrapConstant_le_pow_pow (Real.log_nonneg (by exact_mod_cast hq)) hC₀
    (fun _ hC ↦ (boxImprovementConstant_pos hq R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een hC).le)
    (one_le_boxStepPrefactor hq R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een)
    (by have := one_le_boxStepExponent he₀₁; omega)
    (fun _ hC ↦ boxBootstrapStep_le_boxStepPrefactor hq R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een hC)
    hM

/-- **A closed-form bound for the named safe-box constant.** For `q ≥ 1`, `J ≥ 0`, `Δ > 0` and
every `M` at least the round count at the initial exponent `e₀ = initialBoxExponent q R J Δ`,
the named safe-box constant `physicalBoxConstantExplicit` is at most
`((A + 1)(1 + C₀))^((4k)^M)`, with `C₀ = initialBoxConstantExplicit q R J Δ`,
`A = boxStepPrefactor` at the truncation constant `latticeTruncationRadiusConstant R J Δ 2`
and `k = boxStepExponent e₀`. Source: proof of Proposition 9.5, `08-scanner.tex`,
lines 681–805. -/
theorem physicalBoxConstantExplicit_le_pow_pow (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) (ct Cent eent Cen een : ℝ) {M : ℕ}
    (hM : boxBootstrapRounds (initialBoxExponent q R J Δ) (Exponents.boxError : ℝ)
      (BootstrapParameters.ell (initialBoxExponent q R J Δ)) ≤ M) :
    physicalBoxConstantExplicit q R J Δ ct Cent eent Cen een ≤
      ((boxStepPrefactor q R (initialBoxExponent_pos_and_lt_one q R J Δ).1
          (initialBoxExponent_pos_and_lt_one q R J Δ).2 J Δ
          (latticeTruncationRadiusConstant R J Δ 2) ct Cent eent Cen een + 1) *
        (1 + initialBoxConstantExplicit q R J Δ)) ^
        ((2 * (2 * boxStepExponent (initialBoxExponent q R J Δ))) ^ M) :=
  physicalBoxBootstrapConstant_le_pow_pow hq R _ _ J Δ _ ct Cent eent Cen een
    (initialBoxConstantExplicit_nonneg q R hq hJ hΔ) hM

end TNLean.PEPS.AreaLaw.Scan
