/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelEventKernel

/-! Boundary consumers for finite families of actual graph channels. -/

open QuantumCircuit TNLean.PEPS.AreaLaw Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

-- Empty labels contribute no actual increment, with no operator hypotheses.
example (G : SimpleGraph ι) (a : Fin 0 → ι)
    (k : Fin 0 → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (∑ i, (siteOscillation q y (spectatorRootChannel (k i) B) -
      siteOscillation q y B)) ≤ 0 := by
  apply (sum_siteOscillation_spectatorRootChannel_sub_le_exp_card G a k
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    hC hc hα hα₁ n (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) y B).trans
  simp

-- Two labels at one anchor count twice, even though the anchor image is a singleton.
example (G : SimpleGraph ι) (a y z : ι) (l : ℕ)
    (hy : y ∈ graphBall G a l) (hz : z ∈ graphBall G a l) :
    ((Finset.univ : Finset (Fin 2)).filter fun _ =>
      y ∈ graphBall G a l ∧ z ∈ graphBall G a l).card = 2 := by
  simp [hy, hz]

-- Distinct positive contractions may share the same anchor; the input is arbitrary.
example (G : SimpleGraph ι) (a : ι) (k : Fin 2 → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, k i ∈ supportedOperators q {x | G.Reachable a x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : Finset.univ.sup (G.dist a) ≤ n)
    (hε : ∀ i l, l ≤ n → ‖k i - siteExpectation q (graphBall G a l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (∑ i, (siteOscillation q y (spectatorRootChannel (k i) B) -
      siteOscillation q y B)) ≤
      4 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
        ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => G.edist a y ≤ l),
          Real.exp (-(c / 2 * (l : ℝ) ^ α)) *
            ∑ z ∈ graphBall G a l, siteOscillation q z B := by
  have h := sum_siteOscillation_spectatorRootChannel_sub_le_exp_card G (fun _ => a) k
    hk₀ hk₁ hk hC hc hα hα₁ n (fun _ => hn) hε y B
  rw [← sum_graphBall_shell_eq_sum_card] at h
  convert h using 1
  simp only [Fin.sum_univ_two]
  ring

-- There are no incidences at a site outside every event's connected component.
example {κ : Type*} [Fintype κ] (G : SimpleGraph ι) (a : κ → ι)
    (y z : ι) (hy : ∀ i, G.edist (a i) y = ⊤) (l : ℕ) :
    (Finset.univ.filter fun i : κ =>
      y ∈ graphBall G (a i) l ∧ z ∈ graphBall G (a i) l).card = 0 := by
  simp [notMem_graphBall_of_edist_eq_top (hy _)]

-- The reordering preserves arbitrary signed weights and site values.
example {κ : Type*} [Fintype κ] (G : SimpleGraph ι) (a : κ → ι)
    (n : ℕ) (y : ι) (d : ι → ℝ) :
    (∑ i, ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => G.edist (a i) y ≤ l),
      (-1 : ℝ) * ∑ z ∈ graphBall G (a i) l, d z) =
      ∑ l ∈ Finset.range (n + 1), (-1 : ℝ) *
        ∑ z, ((Finset.univ.filter fun i : κ =>
          y ∈ graphBall G (a i) l ∧ z ∈ graphBall G (a i) l).card : ℝ) * d z :=
  sum_graphBall_shell_eq_sum_card G a n (fun _ => -1) y d

/--
info: 'TNLean.PEPS.AreaLaw.sum_graphBall_shell_eq_sum_card'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_graphBall_shell_eq_sum_card

/--
info: 'TNLean.PEPS.AreaLaw.sum_siteOscillation_spectatorRootChannel_sub_le_exp_card'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_siteOscillation_spectatorRootChannel_sub_le_exp_card
