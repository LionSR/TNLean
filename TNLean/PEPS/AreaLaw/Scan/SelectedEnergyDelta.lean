/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.NormNum

/-!
# The energy estimate from a selected density bound

This scalar auxiliary separates the principal density from its replica remainder.
The signed ground-energy and additive remainder terms are retained exactly.
No scanner structure, exponent choice or new physical assumption is used.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 9.2, `08-scanner.tex`, lines 492–533, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- The eighth root of the density remainder contributes a separate vanishing
energy remainder. The interpolation factor is bounded above using only `0 ≤ p`;
the physical upper bound `p ≤ 1` is not required for this scalar implication.
Source: Proposition 9.2, `scanner:energy-output`, lines 492–533. -/
theorem selectedEnergy_le_of_density_le_add
    {density δ ρ energy e A p ε tail rem gap : ℝ}
    (hdensity : 0 ≤ density) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hbound : density ≤ δ + ρ) (hgap : 0 < gap)
    (hA : 0 ≤ A) (htail : 0 ≤ tail) (hp : 0 ≤ p) (hpε : p ≤ ε)
    (henergy : energy ≤
      (e + A * ((1 - p) * density ^ (1 / 8 : ℝ) + (1 - p) * tail + p) + rem) / gap) :
    energy ≤ A / gap * (δ ^ (1 / 8 : ℝ) + ε + tail) + e / gap +
      (A * ρ ^ (1 / 8 : ℝ) + rem) / gap := by
  have hroot : density ^ (1 / 8 : ℝ) ≤ δ ^ (1 / 8 : ℝ) + ρ ^ (1 / 8 : ℝ) :=
    (Real.rpow_le_rpow hdensity hbound (by norm_num)).trans
      (Real.rpow_add_le_add_rpow hδ hρ (by norm_num) (by norm_num))
  have hsum : (1 - p) * density ^ (1 / 8 : ℝ) + (1 - p) * tail + p ≤
      δ ^ (1 / 8 : ℝ) + ρ ^ (1 / 8 : ℝ) + tail + ε := by
    nlinarith only [hroot, hpε,
      mul_nonneg hp (Real.rpow_nonneg hdensity (1 / 8 : ℝ)), mul_nonneg hp htail]
  refine henergy.trans ((div_le_div_of_nonneg_right
    (_root_.add_le_add (_root_.add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hsum hA)) le_rfl)
    hgap.le).trans_eq ?_)
  ring

/-- With the physical system and coefficients fixed, the density remainder
produces a vanishing energy remainder. Signed remainders are bounded in absolute
value before the eighth root is taken.
The scalar statement holds for every real `gap` under totalized division;
at `gap = 0` the remainder is identically zero. The physical application has
`0 < gap`; no zero-gap physical quotient is asserted.
Source: Proposition 9.2, `08-scanner.tex`, lines 492–533 and 395–397. -/
theorem tendsto_selectedEnergy_remainder
    {ι : Type*} {l : Filter ι} {ρ rem : ι → ℝ}
    (hρ : Filter.Tendsto ρ l (𝓝 0)) (hrem : Filter.Tendsto rem l (𝓝 0))
    (A gap : ℝ) :
    Filter.Tendsto (fun k ↦ (A * |ρ k| ^ (1 / 8 : ℝ) + rem k) / gap) l (𝓝 0) := by
  have habs : Filter.Tendsto (fun k ↦ |ρ k|) l (𝓝 0) := by
    simpa only [abs_zero] using hρ.abs
  have hroot : Filter.Tendsto (fun k ↦ |ρ k| ^ (1 / 8 : ℝ)) l (𝓝 0) :=
    habs.rpow_const_nhds_zero (by norm_num)
  simpa only [mul_zero, add_zero, zero_div] using
    ((hroot.const_mul A).add hrem).div_const gap

end TNLean.PEPS.AreaLaw.Scan
