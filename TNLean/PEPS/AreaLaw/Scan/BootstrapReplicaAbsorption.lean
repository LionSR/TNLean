/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ExplicitThresholds
import TNLean.PEPS.AreaLaw.Scan.BootstrapParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Replica limits and entropy absorption in the rectangle bootstrap

At a fixed physical scale, the two rough norm comparisons contain the same
entropy for every replica count. Vanishing remainders can therefore be removed
before the coefficient loss is absorbed. Neither comparison value nor defect
sequence needs to converge. A separate numerical estimate then chooses the
large-scale threshold for the manuscript's defect and auxiliary scales; it is
given explicitly by `bootstrapComparisonLossThreshold`.

The norm comparisons are explicit hypotheses of the scalar theorem. Their
physical proofs, the common vector and label sequence, and the substitutions
of the typical entropy and auxiliary dimension are not supplied by this module.
Those substitutions must already be included in the two additive budgets.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:bootstrap-energy` and `scanner:bootstrap-comparison`,
lines 744–769, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Filter
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- The fixed entropy is bounded after taking the replica limit in both rough
comparisons and using their coefficient margin. The three remainders vanish
at the fixed physical scale; the additive budgets include any typical-entropy
and auxiliary-dimension substitutions.
Source: `08-scanner.tex`, lines 755–769, `scanner:bootstrap-comparison`. -/
theorem entropy_le_of_replica_comparisons
    {S C τ E Bᵤ Bₗ : ℝ} {F d rᵤ rₗ rₑ : ℕ → ℝ}
    (hS : 0 ≤ S) (hC : 0 ≤ C) (hτ : 0 < τ)
    (hsmall : C * (τ + E / τ) ≤ 1)
    (hrᵤ : Tendsto rᵤ atTop (𝓝 0))
    (hrₗ : Tendsto rₗ atTop (𝓝 0))
    (hrₑ : Tendsto rₑ atTop (𝓝 0))
    (hdefect : ∀ᶠ k in atTop, d k ≤ E + rₑ k)
    (hupper : ∀ᶠ k in atTop, F k ≤ 2 * S + Bᵤ + rᵤ k)
    (hlower : ∀ᶠ k in atTop,
      (4 - C * (τ + d k / τ)) * S - Bₗ - rₗ k ≤ F k) :
    S ≤ Bᵤ + Bₗ := by
  have hbound : ∀ᶠ k in atTop,
      (2 - C * (τ + E / τ)) * S ≤
        Bᵤ + Bₗ + rᵤ k + rₗ k + (C / τ) * S * rₑ k := by
    filter_upwards [hdefect, hupper, hlower] with k hd hu hl
    have hquot : d k / τ ≤ (E + rₑ k) / τ :=
      div_le_div_of_nonneg_right hd hτ.le
    have hloss : C * (τ + d k / τ) * S ≤
        C * (τ + (E + rₑ k) / τ) * S :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl τ) hquot) hC) hS
    have hsplit : C * (τ + (E + rₑ k) / τ) * S =
        C * (τ + E / τ) * S + (C / τ) * S * rₑ k := by ring
    rw [hsplit] at hloss
    nlinarith only [hu, hl, hloss]
  have hlimit : Tendsto
      (fun k ↦ Bᵤ + Bₗ + rᵤ k + rₗ k + (C / τ) * S * rₑ k)
      atTop (𝓝 (Bᵤ + Bₗ)) := by
    simpa only [add_zero, mul_zero] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ Bᵤ + Bₗ) atTop
        (𝓝 (Bᵤ + Bₗ))).add hrᵤ).add hrₗ).add (hrₑ.const_mul ((C / τ) * S))
  have hlim := le_of_tendsto_of_tendsto tendsto_const_nhds hlimit hbound
  have hmargin : 1 ≤ 2 - C * (τ + E / τ) := by linarith only [hsmall]
  exact (le_mul_of_one_le_left hS hmargin).trans hlim

/-- The explicit threshold `⌈max 1 (max 3 (C (1 + Cₑ)) ^ (4 / ν))⌉₊` beyond which
`n ^ (ν / 4) ≥ max 3 (C (1 + Cₑ))`, with `ν = ν(e₀)` the fixed bootstrap error exponent
(`08-scanner.tex`, lines 744–769). -/
noncomputable def bootstrapComparisonLossThreshold (C Cₑ e₀ : ℝ) : ℕ :=
  Real.natRpowThreshold (BootstrapParameters.nu e₀ / 4) (max 3 (C * (1 + Cₑ)))

/-- With the fixed bootstrap error exponent, at every `n` from the explicit threshold
`bootstrapComparisonLossThreshold C Cₑ e₀` on, the relative coefficient loss is at most one
and the auxiliary fraction lies below one half.
Source: `08-scanner.tex`, lines 744–769, `scanner:bootstrap-energy`. -/
theorem bootstrap_comparison_loss_of_threshold_le (C Cₑ : ℝ) {e₀ : ℝ}
    (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) {n : ℕ}
    (hthr : bootstrapComparisonLossThreshold C Cₑ e₀ ≤ n) :
    let τ := (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4)
    let E := Cₑ * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2)
    0 < τ ∧ τ < 1 / 2 ∧ C * (τ + E / τ) ≤ 1 := by
  obtain ⟨hg₀, _, _, _, _⟩ := BootstrapParameters.parameter_bounds he₀ he₀₁
  have hν₄ : 0 < BootstrapParameters.nu e₀ / 4 := div_pos (div_pos hg₀ (by norm_num)) (by norm_num)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Real.one_le_natRpowThreshold _ _).trans hthr
  have hpow := Real.le_natCast_rpow_of_natRpowThreshold_le hν₄ hthr
  have hP : 0 < (n : ℝ) ^ (BootstrapParameters.nu e₀ / 4) := Real.rpow_pos_of_pos hnpos _
  have hτ : (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4) =
      ((n : ℝ) ^ (BootstrapParameters.nu e₀ / 4))⁻¹ := by
    rw [neg_div, Real.rpow_neg hnpos.le]
  dsimp only
  refine ⟨Real.rpow_pos_of_pos hnpos _, ?_, ?_⟩
  · rw [hτ, inv_lt_comm₀ hP (by norm_num)]
    linarith [le_max_left 3 (C * (1 + Cₑ))]
  have hsplit : C * ((n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4) +
      Cₑ * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2) /
        (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4)) =
      C * (1 + Cₑ) * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4) := by
    rw [mul_div_assoc, ← Real.rpow_sub hnpos,
      show -BootstrapParameters.nu e₀ / 2 - (-BootstrapParameters.nu e₀ / 4) =
        -BootstrapParameters.nu e₀ / 4 by ring]
    ring
  rw [hsplit, hτ, ← div_eq_mul_inv, div_le_one hP]
  exact (le_max_right _ _).trans hpow

/-- With the fixed bootstrap error exponent, one threshold makes the relative
coefficient loss at most one and the auxiliary fraction lie below one half.
This threshold is chosen after the fixed-scale
replica limit; it requires no replica convergence rate uniform in the scale.
Source: `08-scanner.tex`, lines 744–769, `scanner:bootstrap-energy`. -/
theorem exists_bootstrap_comparison_loss_threshold (C Cₑ : ℝ) {e₀ : ℝ}
    (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let τ := (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4)
      let E := Cₑ * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2)
      0 < τ ∧ τ < 1 / 2 ∧ C * (τ + E / τ) ≤ 1 :=
  ⟨_, Real.one_le_natRpowThreshold _ _,
    fun _ => bootstrap_comparison_loss_of_threshold_le C Cₑ he₀ he₀₁⟩

end TNLean.PEPS.AreaLaw.Scan
