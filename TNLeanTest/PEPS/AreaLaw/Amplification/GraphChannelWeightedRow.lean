/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelWeightedRow

/-! Strict boundary consumers for the actual graph-ball weighted row estimate. -/

open QuantumCircuit TNLean.PEPS.AreaLaw
open scoped BigOperators

namespace GraphChannelWeightedRowTest

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

-- Empty label types contribute zero at every cutoff, without sign assumptions.
theorem emptyLabels (G : SimpleGraph ι) (a : Fin 0 → ι) (D b α : ℝ) (N : ℕ) (y : ι) :
    (∑ z, graphChannelEventKernel G a D b α N y z *
      Real.exp (b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)) = 0 := by
  simp [graphChannelEventKernel]

-- At cutoff zero the anchor multiplicity is still exactly two.
theorem repeatedAnchor_zeroCutoff (G : SimpleGraph ι) (x : ι)
    (D b : ℝ) {α : ℝ} (hα : 0 < α) :
    graphChannelEventKernel G (fun _ : Fin 2 => x) D b α 0 x x = 2 * D := by
  simp [graphChannelEventKernel, mem_graphBall, Real.zero_rpow hα.ne', mul_comm]

-- Both coincident labels are admitted by the weighted row theorem itself.
theorem repeatedAnchorRows (G : SimpleGraph ι) (x y : ι) {D K b α : ℝ}
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hb : 0 < b) (hα : 0 < α)
    (hball : ∀ z l, ((graphBall G z l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (N : ℕ) :
    (∑ z, graphChannelEventKernel G (fun _ : Fin 2 => x) D b α N y z *
      Real.exp (b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)) ≤
      D * 2 * K ^ 2 * ∑ l ∈ Finset.range (N + 1), ((l : ℝ) + 1) ^ 4 *
        Real.exp (-(b / 2 * (l : ℝ) ^ α)) := by
  apply sum_graphChannelEventKernel_mul_exp_le G (fun _ : Fin 2 => x)
    hD hK (by norm_num) hb hα hball
  intro z
  exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset (Fin 2)) fun _ => x = z)

-- Zero cutoff is included, and the fourth-power finite sum reduces to one.
theorem zeroCutoff (G : SimpleGraph ι) (a : κ → ι) {D K μ b α : ℝ}
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hb : 0 < b) (hα : 0 < α)
    (hball : ∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (hfiber : ∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ)
    (y : ι) :
    (∑ z, graphChannelEventKernel G a D b α 0 y z *
      Real.exp (b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)) ≤ D * μ * K ^ 2 := by
  simpa [Real.zero_rpow hα.ne'] using
    sum_graphChannelEventKernel_mul_exp_le G a hD hK hμ hb hα hball hfiber 0 y

-- The disconnected two-site graph has zero off-diagonal kernel even though
-- its natural graph distance is zero there.
theorem disconnected (D b α : ℝ) (N : ℕ) :
    graphChannelEventKernel (⊥ : SimpleGraph (Fin 2)) id D b α N 0 1 = 0 := by
  apply graphChannelEventKernel_eq_zero_of_not_reachable
  simp [SimpleGraph.reachable_bot]

example : (⊥ : SimpleGraph (Fin 2)).dist 0 1 = 0 := by
  simp [SimpleGraph.dist, SimpleGraph.edist_bot]

-- The witness is selected before either finite type, graph, labels, or cutoff.
example {D K μ b α : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K) (hμ : 0 ≤ μ)
    (hb : 0 < b) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
      (G : SimpleGraph ι) (a : κ → ι),
      (∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) →
      (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
      ∀ (N : ℕ) (y : ι),
        (∑ z, graphChannelEventKernel G a D b α N y z *
          Real.exp (b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)) ≤ C :=
  exists_graphChannelEventKernel_weighted_row_le hD hK hμ hb hα

end GraphChannelWeightedRowTest

/--
info: 'TNLean.PEPS.AreaLaw.graphChannelEventKernel_eq_zero_of_not_reachable'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms graphChannelEventKernel_eq_zero_of_not_reachable

/--
info: 'TNLean.PEPS.AreaLaw.sum_graphChannelEventKernel_mul_exp_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_graphChannelEventKernel_mul_exp_le

/--
info: 'TNLean.PEPS.AreaLaw.exists_graphChannelEventKernel_weighted_row_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_graphChannelEventKernel_weighted_row_le

/--
info: 'GraphChannelWeightedRowTest.emptyLabels'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphChannelWeightedRowTest.emptyLabels

/--
info: 'GraphChannelWeightedRowTest.repeatedAnchor_zeroCutoff'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphChannelWeightedRowTest.repeatedAnchor_zeroCutoff

/--
info: 'GraphChannelWeightedRowTest.repeatedAnchorRows'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphChannelWeightedRowTest.repeatedAnchorRows

/--
info: 'GraphChannelWeightedRowTest.zeroCutoff'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphChannelWeightedRowTest.zeroCutoff

/--
info: 'GraphChannelWeightedRowTest.disconnected'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphChannelWeightedRowTest.disconnected
