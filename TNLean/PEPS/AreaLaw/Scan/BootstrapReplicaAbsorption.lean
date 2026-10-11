/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
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
large-scale threshold for the manuscript's defect and auxiliary scales.

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
      0 < τ ∧ τ < 1 / 2 ∧ C * (τ + E / τ) ≤ 1 := by
  obtain ⟨hg₀, _, _, _, _⟩ := BootstrapParameters.parameter_bounds he₀ he₀₁
  have hν : 0 < BootstrapParameters.nu e₀ := div_pos hg₀ (by norm_num)
  have hτlimit : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (div_pos hν (by norm_num : (0 : ℝ) < 4))).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    refine h.congr' (Eventually.of_forall fun n ↦ ?_)
    simp only [Function.comp_apply, neg_div]
  have hlimit : Tendsto
      (fun n : ℕ ↦ C * (1 + Cₑ) * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hτlimit.const_mul (C * (1 + Cₑ))
  have heventual := (hτlimit.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).and
    (hlimit.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := heventual.exists_forall_of_atTop
  refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
  have hn₁ : 1 ≤ n := (le_max_right N 1).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn₁)
  dsimp only
  have hscale := hN n ((le_max_left N 1).trans hn)
  refine ⟨Real.rpow_pos_of_pos hnpos _, hscale.1, ?_⟩
  have hsplit : C * ((n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4) +
      Cₑ * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2) /
        (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4)) =
      C * (1 + Cₑ) * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4) := by
    rw [mul_div_assoc, ← Real.rpow_sub hnpos,
      show -BootstrapParameters.nu e₀ / 2 - (-BootstrapParameters.nu e₀ / 4) =
        -BootstrapParameters.nu e₀ / 4 by ring]
    ring
  rw [hsplit]
  exact hscale.2.le

end TNLean.PEPS.AreaLaw.Scan
