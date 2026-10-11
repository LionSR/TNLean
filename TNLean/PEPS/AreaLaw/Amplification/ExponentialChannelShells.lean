/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.LocalChannelOscillation
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Stretched-exponential bounds for actual local-channel shells

Localization errors `C exp (-c l^α)` give the actual shell coefficient the bound
`(2 + 8 √C exp (c / 2)) exp (-(c / 2) l^α)`, including radius zero.
The same explicit coefficients bound the physical shell oscillations and the
finite one-event oscillation increment, uniformly in arbitrary finite spectators.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 101–139, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are finite-radius statements for increasing regions; no graph metric,
infinite-radius limit, spatial propagation, or clock process is asserted.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- Explicit constants in the stretched-exponential channel-shell estimate,
including the zeroth shell. Source: area law, `eq:amplification-channel-shells`,
`09-amplification.tex`, lines 101–106. -/
theorem localRootChannelShellBound_le_exp {C c α : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) (l : ℕ) :
    localRootChannelShellBound (fun j => C * Real.exp (-(c * (j : ℝ) ^ α))) l ≤
      (2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
        Real.exp (-(c / 2 * (l : ℝ) ^ α)) := by
  have hsqrt (j : ℕ) :
      Real.sqrt (C * Real.exp (-(c * (j : ℝ) ^ α))) =
        Real.sqrt C * Real.exp (-(c / 2 * (j : ℝ) ^ α)) := by
    rw [Real.sqrt_mul hC, ← Real.exp_half]
    congr 2
    ring
  cases l with
  | zero =>
    simpa only [localRootChannelShellBound, Nat.cast_zero, Real.zero_rpow hα.ne',
      mul_zero, neg_zero, Real.exp_zero, mul_one] using
      le_add_of_nonneg_right (show 0 ≤ 8 * Real.sqrt C * Real.exp (c / 2) by positivity)
  | succ n =>
    have hstep : ((n + 1 : ℕ) : ℝ) ^ α ≤ (n : ℝ) ^ α + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one, Real.one_rpow] using
        Real.rpow_add_le_add_rpow (Nat.cast_nonneg n) (show (0 : ℝ) ≤ 1 by norm_num)
          hα.le hα₁
    have hprev : Real.exp (-(c / 2 * (n : ℝ) ^ α)) ≤
        Real.exp (c / 2) * Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hstep (show 0 ≤ c / 2 by positivity)]
    have hnext : Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)) ≤
        Real.exp (c / 2) * Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)) :=
      le_mul_of_one_le_left (Real.exp_pos _).le
        (Real.one_le_exp_iff.mpr (by positivity))
    simp only [localRootChannelShellBound, hsqrt]
    calc
      _ ≤ 4 * (Real.sqrt C *
              (Real.exp (c / 2) * Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α))) +
            Real.sqrt C *
              (Real.exp (c / 2) * Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hnext (Real.sqrt_nonneg C))
            (mul_le_mul_of_nonneg_left hprev (Real.sqrt_nonneg C))) (by norm_num)
      _ = (8 * Real.sqrt C * Real.exp (c / 2)) *
          Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- Stretched-exponential localization errors of a positive contraction imply
an explicit shell bound by the physical oscillations in its region. Source:
area law, `eq:amplification-shell-oscillation`, lines 109–121. -/
theorem norm_localRootChannelShell_le_exp_sum_siteOscillation
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (l : ℕ)
    (hε : ∀ j ≤ l, ‖k - siteExpectation q (regions j) k‖ ≤
      C * Real.exp (-(c * (j : ℝ) ^ α)))
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannelShell regions k l B‖ ≤
      ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
        Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
          ∑ z ∈ regions l, siteOscillation q z B := by
  apply (norm_localRootChannelShell_le_sum_siteOscillation
    regions hregions hk₀ hk₁ _ l hε B).trans
  exact mul_le_mul_of_nonneg_right (localRootChannelShellBound_le_exp hC hc hα hα₁ l)
    (Finset.sum_nonneg fun z _ => siteOscillation_nonneg z B)

/-- The finite one-event oscillation increment with explicit stretched-exponential
coefficients, using only actual localization errors through the cutoff. Shells
contribute precisely when their region contains the observed site. Source:
area law, `eq:amplification-oscillation-increment`, lines 124–139. -/
theorem siteOscillation_localRootChannel_le_exp
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (regions l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (localRootChannel (regions n) k B) ≤
      siteOscillation q y B +
        2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l => y ∈ regions l),
          ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
            Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
              ∑ z ∈ regions l, siteOscillation q z B := by
  apply (siteOscillation_localRootChannel_le regions hregions hk₀ hk₁ _ n hε y B).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul_of_nonneg_right (localRootChannelShellBound_le_exp hC hc hα hα₁ l)
    (Finset.sum_nonneg fun z _ => siteOscillation_nonneg z B)

end TNLean.PEPS.AreaLaw
