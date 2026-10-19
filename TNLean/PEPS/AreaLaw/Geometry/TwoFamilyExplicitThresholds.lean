/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ExplicitThresholds
import TNLean.PEPS.AreaLaw.Geometry.DyadicScales

/-!
# Explicit thresholds for the two-family decomposition

The proof of Proposition 11.2 fixes a stopping scale and a lower layer index
above several "sufficiently large" thresholds (`10-geometry.tex`, lines
756–774). The source never quantifies them. This module gives each one a
closed form built from the power-ratio threshold of
`TNLean.Algebra.ExplicitThresholds`, and proves the corresponding inequality
above it.

## Main definitions

* `dyadicIndexThreshold T = Nat.clog 2 ⌈T⌉₊`, which is `0` for `T ≤ 1` and
  `⌈log₂ ⌈T⌉⌉` otherwise: from it on, `T ≤ 2 ^ k`.
* `fineScaleIndexThreshold U = ⌈dyadicIndexThreshold U / ζ⌉`: from it on,
  `U ≤ 2 ^ ⌊ζ k⌋`.
* `fineClearanceThreshold c₁ C_B`: from it on, `2 ⌈C_B u⌉ ^ β < c₁ u ^ ρ₀`.
* `beltReplacementScaleThreshold C_B ε`: from it on,
  `⌊⌈C_B u⌉ ^ (1 - ℓ)⌋ ≤ ε u`.

The primary thresholds `primaryScaleLimitThreshold` and
`primaryScannerScaleThreshold` live with the primary scanner scale in
`TNLean.PEPS.AreaLaw.Geometry.PrimaryBirthTemplates`. The eventual statements
`eventually_fine_clearance` and `eventually_beltReplacementScaleLimit` are
derived from the explicit ones here.

These are auxiliary to the explicit value of the constant in Theorem 1.1. The
source asserts only the existence of that constant (`00-introduction.tex`,
lines 39–53), so none of these definitions formalizes a source label.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `10-geometry.tex`, primary scale limits
  lines 722–729, belt and replacement scales lines 732–740, and threshold
  order lines 756–774.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### Dyadic indices -/

/-- The least dyadic index `k` with `⌈T⌉₊ ≤ 2 ^ k`: it is `0` for `T ≤ 1` and
`⌈log₂ ⌈T⌉⌉` otherwise. -/
def dyadicIndexThreshold (T : ℝ) : ℕ :=
  Nat.clog 2 ⌈T⌉₊

/-- From `dyadicIndexThreshold T` on, `T ≤ 2 ^ k`. -/
theorem le_two_pow_of_dyadicIndexThreshold_le {T : ℝ} {k : ℕ}
    (hk : dyadicIndexThreshold T ≤ k) : T ≤ (2 : ℝ) ^ k := by
  have h : ⌈T⌉₊ ≤ 2 ^ k := (Nat.clog_le_iff_le_pow one_lt_two).mp hk
  calc T ≤ ⌈T⌉₊ := Nat.le_ceil T
    _ ≤ (2 : ℝ) ^ k := by exact_mod_cast h

/-- The layer threshold `⌈dyadicIndexThreshold U / ζ⌉` for the fine scale
`t_k = 2 ^ ⌊ζ k⌋` to reach `U`. -/
def fineScaleIndexThreshold (U : ℝ) : ℕ :=
  ⌈(dyadicIndexThreshold U : ℝ) / (Exponents.zeta : ℝ)⌉₊

/-- **Explicit fine-scale threshold.** From `fineScaleIndexThreshold U` on,
`U ≤ 2 ^ ⌊ζ k⌋`. Explicit form of the initial-belt part of the threshold choice
following `geometry:fine-clearance`, `10-geometry.tex`, lines 761–771. -/
theorem le_two_pow_fineScaleIndex_of_fineScaleIndexThreshold_le {U : ℝ} {k : ℕ}
    (hk : fineScaleIndexThreshold U ≤ k) : U ≤ (2 : ℝ) ^ fineScaleIndex k := by
  have hζ : 0 < (Exponents.zeta : ℝ) := by
    norm_num [Exponents.zeta, Exponents.geometryDelta]
  have hdiv : (dyadicIndexThreshold U : ℝ) / Exponents.zeta ≤ k :=
    Nat.ceil_le.mp hk
  have hL : dyadicIndexThreshold U ≤ fineScaleIndex k := by
    apply Nat.le_floor
    rw [div_le_iff₀ hζ] at hdiv
    linarith
  exact le_two_pow_of_dyadicIndexThreshold_le hL

/-! ### Belt and replacement scales -/

/-- The scale threshold for the fine-clearance inequality: the power-ratio
threshold for `2 (C_B + 1) ^ β u ^ β ≤ (c₁ / 2) u ^ ρ₀`. Since
`ρ₀ - β = 10⁻⁶`, it is of order `(4 (C_B + 1) ^ β / c₁) ^ 1000000`. -/
def fineClearanceThreshold (c₁ CB : ℝ) : ℝ :=
  Real.powerRatioThreshold (2 * (CB + 1) ^ (Exponents.beta : ℝ)) (c₁ / 2)
    ((Exponents.rho : ℝ) - Exponents.beta)

/-- **Explicit fine clearance** (`geometry:fine-clearance`). For `c₁ > 0` and
`C_B ≥ 0`, every `u ≥ fineClearanceThreshold c₁ C_B` satisfies
`2 ⌈C_B u⌉ ^ β < c₁ u ^ ρ₀`.
Source: area-law Section 11, `10-geometry.tex`, lines 761–768. -/
theorem fine_clearance_of_fineClearanceThreshold_le {c₁ CB u : ℝ} (hc₁ : 0 < c₁)
    (hCB : 0 ≤ CB) (hu : fineClearanceThreshold c₁ CB ≤ u) :
    2 * (⌈CB * u⌉₊ : ℝ) ^ (Exponents.beta : ℝ) < c₁ * u ^ (Exponents.rho : ℝ) := by
  have hβ : 0 < (Exponents.beta : ℝ) := by
    norm_num [Exponents.beta, Exponents.boxError]
  have hβρ : (Exponents.beta : ℝ) < (Exponents.rho : ℝ) := by
    exact_mod_cast Exponents.geometry_gaps.2.2.2.2.1
  have hu1 : 1 ≤ u := (Real.one_le_powerRatioThreshold _ _ _).trans hu
  have hu0 : 0 < u := by linarith
  have hceil : (⌈CB * u⌉₊ : ℝ) ≤ (CB + 1) * u := by
    have := Nat.ceil_lt_add_one (mul_nonneg hCB hu0.le)
    nlinarith
  have hmain := Real.mul_rpow_le_mul_rpow_of_powerRatioThreshold_le
    (by positivity : (0 : ℝ) ≤ 2 * (CB + 1) ^ (Exponents.beta : ℝ)) (half_pos hc₁) hβρ hu
  have hρpos : 0 < u ^ (Exponents.rho : ℝ) := Real.rpow_pos_of_pos hu0 _
  calc 2 * (⌈CB * u⌉₊ : ℝ) ^ (Exponents.beta : ℝ)
      ≤ 2 * ((CB + 1) * u) ^ (Exponents.beta : ℝ) := by gcongr
    _ = 2 * (CB + 1) ^ (Exponents.beta : ℝ) * u ^ (Exponents.beta : ℝ) := by
        rw [Real.mul_rpow (by linarith) hu0.le]
        ring
    _ ≤ c₁ / 2 * u ^ (Exponents.rho : ℝ) := hmain
    _ < c₁ * u ^ (Exponents.rho : ℝ) := by nlinarith

/-- The scale threshold for the belt and replacement dilation count: the
power-ratio threshold for `B ^ (1 - ℓ) u ^ (1 - ℓ) ≤ ε u` with
`B = max C_B 0 + 1`. Since `ℓ = 10⁻⁵`, it is of order
`(B ^ (1 - ℓ) / ε) ^ 100000`. -/
def beltReplacementScaleThreshold (CB ε : ℝ) : ℝ :=
  Real.powerRatioThreshold ((max CB 0 + 1) ^ (1 - (Exponents.geometryEll : ℝ))) ε
    (Exponents.geometryEll : ℝ)

/-- **Explicit dilation count for belts and replacements.** For `ε > 0`, every
`u ≥ beltReplacementScaleThreshold C_B ε` satisfies `⌊⌈C_B u⌉ ^ (1 - ℓ)⌋ ≤ ε u`.
Source: area-law
Section 11, `10-geometry.tex`, line 740, with `L = ⌊n ^ (1 - ℓ)⌋` as in
`geometry:primary-limits` (lines 725–729). -/
theorem beltReplacementScaleLimit_of_beltReplacementScaleThreshold_le (CB : ℝ) {ε u : ℝ}
    (hε : 0 < ε) (hu : beltReplacementScaleThreshold CB ε ≤ u) :
    (⌊(⌈CB * u⌉₊ : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ : ℝ) ≤ ε * u := by
  have hℓ1 : (0 : ℝ) ≤ 1 - Exponents.geometryEll := by norm_num [Exponents.geometryEll]
  have hℓlt : 1 - (Exponents.geometryEll : ℝ) < 1 := by
    norm_num [Exponents.geometryEll]
  set e : ℝ := 1 - (Exponents.geometryEll : ℝ)
  set B : ℝ := max CB 0 + 1
  have hB : 0 < B := by positivity
  have hu1 : 1 ≤ u := (Real.one_le_powerRatioThreshold _ _ _).trans hu
  have hu0 : 0 < u := by linarith
  have hceil : (⌈CB * u⌉₊ : ℝ) ≤ B * u := by
    have hmono : (⌈CB * u⌉₊ : ℝ) ≤ ⌈max CB 0 * u⌉₊ := by
      exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left CB 0) hu0.le)
    have hlt := Nat.ceil_lt_add_one (mul_nonneg (le_max_right CB 0) hu0.le)
    nlinarith
  have hgap : (1 : ℝ) - e = Exponents.geometryEll := by ring
  have hmain := Real.mul_rpow_le_mul_rpow_of_powerRatioThreshold_le
    (x := u) (by positivity : (0 : ℝ) ≤ B ^ e) hε hℓlt (by rw [hgap]; exact hu)
  calc (⌊(⌈CB * u⌉₊ : ℝ) ^ e⌋₊ : ℝ) ≤ (⌈CB * u⌉₊ : ℝ) ^ e :=
        Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) e)
    _ ≤ (B * u) ^ e := Real.rpow_le_rpow (Nat.cast_nonneg _) hceil hℓ1
    _ = B ^ e * u ^ e := Real.mul_rpow hB.le hu0.le
    _ ≤ ε * u ^ (1 : ℝ) := hmain
    _ = ε * u := by rw [Real.rpow_one]

end TNLean.PEPS.AreaLaw.Geometry
