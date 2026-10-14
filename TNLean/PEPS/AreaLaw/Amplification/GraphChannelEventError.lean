/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ExponentialChannelShells
import TNLean.PEPS.AreaLaw.Amplification.ComponentChannelOscillation

/-!
# One-event errors from actual channel shells

Summing the actual localized channel shells bounds the operator-norm error of
a root channel by the physical site oscillations. At a finite radius containing
the anchor component, the localized channel equals the full channel exactly.
The coefficient is the shell coefficient itself, without the extra factor two
needed when bounding a site-oscillation increment.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 101–121 and 203–215, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

variable {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
  [Fintype Aux] [DecidableEq Aux]

/-- The finite shell sum controls the actual localized channel error in
operator norm. Source: area law, `09-amplification.tex`, lines 101–121,203–215. -/
theorem norm_localRootChannel_sub_self_le_exp_sum_siteOscillation
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (regions l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannel (regions n) k B - B‖ ≤
      ∑ l ∈ Finset.range (n + 1),
        ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
          Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
            ∑ z ∈ regions l, siteOscillation q z B := by
  revert hε
  induction n with
  | zero =>
    intro hε
    simpa only [localRootChannelShell, Nat.zero_add, Finset.sum_range_one] using
      norm_localRootChannelShell_le_exp_sum_siteOscillation
        regions hregions hk₀ hk₁ hC hc hα hα₁ 0 hε B
  | succ n ih =>
    intro hε
    have hprev := ih fun l hl => hε l (hl.trans (Nat.le_succ n))
    have hnext := norm_localRootChannelShell_le_exp_sum_siteOscillation
      regions hregions hk₀ hk₁ hC hc hα hα₁ (n + 1) hε B
    change ‖localRootChannel (regions (n + 1)) k B -
      localRootChannel (regions n) k B‖ ≤ _ at hnext
    rw [Finset.sum_range_succ]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (localRootChannel (regions n) k B) _).trans
      ((add_le_add hnext hprev).trans_eq (add_comm _ _))

/-- Once the graph-ball cutoff contains the anchor component, the finite shell
bound controls the full physical event error. Source: area law,
`09-amplification.tex`, lines 135–139,203–215. -/
theorem norm_spectatorRootChannel_sub_self_le_exp_of_component_support
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : Finset.univ.sup (G.dist a) ≤ n)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (graphBall G a l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖spectatorRootChannel k B - B‖ ≤
      ∑ l ∈ Finset.range (n + 1),
        ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
          Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
            ∑ z ∈ graphBall G a l, siteOscillation q z B := by
  simpa only [localRootChannel_graphBall_eq_of_component_support G a hk hn] using
    norm_localRootChannel_sub_self_le_exp_sum_siteOscillation
      (graphBall G a) (graphBall_mono G a) hk₀ hk₁ hC hc hα hα₁ n hε B

end TNLean.PEPS.AreaLaw
