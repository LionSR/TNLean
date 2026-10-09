/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelOscillation

/-! Boundary consumers for the full graph-channel exponential estimate. -/

open QuantumCircuit TNLean.PEPS.AreaLaw Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

-- The finite sum vanishes across components; no real conversion of infinity occurs.
example (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : Finset.univ.sup (G.dist a) ≤ n)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (graphBall G a l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (hy : G.edist a y = ⊤)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (spectatorRootChannel k B) ≤ siteOscillation q y B := by
  simpa [hy] using siteOscillation_spectatorRootChannel_le_exp_of_component_support
    G a hk₀ hk₁ hk hC hc hα hα₁ n hn hε y B

-- The graph estimate preserves zero physical oscillation of any spectator-only input.
example (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : Finset.univ.sup (G.dist a) ≤ n)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (graphBall G a l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (T : Matrix Aux Aux ℂ) :
    siteOscillation q y
      (spectatorRootChannel k ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ T)) = 0 := by
  apply le_antisymm _ (siteOscillation_nonneg _ _)
  simpa only [siteOscillation_one_kronecker, Finset.sum_const_zero, mul_zero, add_zero] using
    siteOscillation_spectatorRootChannel_le_exp_of_component_support
      G a hk₀ hk₁ hk hC hc hα hα₁ n hn hε y
        ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ T)

-- Every finite spectator, including the zero-dimensional one, is admitted by the API.
example (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : Finset.univ.sup (G.dist a) ≤ n)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (graphBall G a l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (B : Matrix ((ι → Fin q) × Fin 0) ((ι → Fin q) × Fin 0) ℂ) :
    siteOscillation q y (spectatorRootChannel k B) ≤ siteOscillation q y B +
      2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => G.edist a y ≤ l),
        ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
          Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
            ∑ z ∈ graphBall G a l, siteOscillation q z B :=
  siteOscillation_spectatorRootChannel_le_exp_of_component_support
    G a hk₀ hk₁ hk hC hc hα hα₁ n hn hε y B

/--
info: 'TNLean.PEPS.AreaLaw.siteOscillation_spectatorRootChannel_le_exp_of_component_support'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms siteOscillation_spectatorRootChannel_le_exp_of_component_support
