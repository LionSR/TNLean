/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelOscillation

/-!
# Finite event-family bounds for full graph channels

The sum of the actual oscillation increments of component-supported root
channels is bounded by a finite weighted ball-incidence count. Labels remain
distinct even when their anchors coincide. The channel estimate applies to
arbitrary operators with arbitrary finite spectators.

The only reordering is of finite sums. No weighted row bound, infinite series,
Hamiltonian propagation, or chronological product estimate is asserted here.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 139–155, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

private theorem sum_graphBall_eq_sum_card (G : SimpleGraph ι) (a : κ → ι)
    (l : ℕ) (y : ι) (d : ι → ℝ) :
    (∑ i, if y ∈ graphBall G (a i) l then ∑ z ∈ graphBall G (a i) l, d z else 0) =
      ∑ z, ((Finset.univ.filter fun i : κ =>
        y ∈ graphBall G (a i) l ∧ z ∈ graphBall G (a i) l).card : ℝ) * d z := by
  classical
  calc
    _ = ∑ i, ∑ z, if y ∈ graphBall G (a i) l ∧ z ∈ graphBall G (a i) l
        then d z else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hy : y ∈ graphBall G (a i) l <;> simp [hy]
    _ = ∑ z, ∑ i, if y ∈ graphBall G (a i) l ∧ z ∈ graphBall G (a i) l
        then d z else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.natCast_card_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

/-- Reorder the finite shell sum into a count of labels whose ball contains
both sites. Repeated anchors retain their full multiplicity. Source: area law,
`09-amplification.tex`, lines 139–146, at a finite cutoff. -/
theorem sum_graphBall_shell_eq_sum_card (G : SimpleGraph ι) (a : κ → ι)
    (n : ℕ) (w : ℕ → ℝ) (y : ι) (d : ι → ℝ) :
    (∑ i, ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => G.edist (a i) y ≤ l),
      w l * ∑ z ∈ graphBall G (a i) l, d z) =
      ∑ l ∈ Finset.range (n + 1), w l *
        ∑ z, ((Finset.univ.filter fun i : κ =>
          y ∈ graphBall G (a i) l ∧ z ∈ graphBall G (a i) l).card : ℝ) * d z := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  calc
    _ = w l * ∑ i, if y ∈ graphBall G (a i) l
        then ∑ z ∈ graphBall G (a i) l, d z else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mem_graphBall, mul_ite, mul_zero]
    _ = _ := by rw [sum_graphBall_eq_sum_card]

variable {q : ℕ} [NeZero q] {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- Sum the actual full-channel oscillation increments over a finite family of
event labels. Uniform actual localization tails and exact component support
give the explicit finite ball-incidence bound. No injectivity of the anchors
or Hermiticity of the input is required. Source: area law,
`09-amplification.tex`, lines 139–146, using the single-event estimate at
lines 124–139. The common cutoff contains every anchor component. -/
theorem sum_siteOscillation_spectatorRootChannel_sub_le_exp_card
    (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, k i ∈ supportedOperators q {x | G.Reachable (a i) x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : ∀ i, Finset.univ.sup (G.dist (a i)) ≤ n)
    (hε : ∀ i l, l ≤ n → ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (∑ i, (siteOscillation q y (spectatorRootChannel (k i) B) -
      siteOscillation q y B)) ≤
      2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
        ∑ l ∈ Finset.range (n + 1), Real.exp (-(c / 2 * (l : ℝ) ^ α)) *
          ∑ z, ((Finset.univ.filter fun i : κ =>
            y ∈ graphBall G (a i) l ∧ z ∈ graphBall G (a i) l).card : ℝ) *
              siteOscillation q z B := by
  classical
  calc
    _ ≤ ∑ i, 2 *
        ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => G.edist (a i) y ≤ l),
          ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
            Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
              ∑ z ∈ graphBall G (a i) l, siteOscillation q z B := by
      apply Finset.sum_le_sum
      intro i _
      exact sub_le_iff_le_add'.mpr
        (siteOscillation_spectatorRootChannel_le_exp_of_component_support
          G (a i) (hk₀ i) (hk₁ i) (hk i) hC hc hα hα₁ n (hn i) (hε i) y B)
    _ = _ := by
      rw [← Finset.mul_sum, sum_graphBall_shell_eq_sum_card]
      simp_rw [mul_assoc, ← Finset.mul_sum]

end TNLean.PEPS.AreaLaw
