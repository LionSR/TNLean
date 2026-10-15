/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedOperatorContraction
import TNLean.PEPS.Approximation.PartyProductScalar

/-!
# Absorbing a scalar into a distributed local matrix

A scalar multiplying the contracted operator can be placed at one supplied
party. The actual links, their alphabets, and all other local matrices are
unchanged. The identity uses no scalar division and includes zero scalars,
empty label alphabets, and zero sample counts. No ambient nonemptiness is
assumed: the chosen party is an explicit argument.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 573–579.
-/

noncomputable section
namespace TNLean.PEPS.Approximation.DistributedOperatorContraction

/-- Placing a scalar in one existing local matrix scales the literal contraction.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 573–579. -/
theorem contractedOperator_smul_at_party
    {P G : Type} [Fintype P] [DecidableEq P] [DecidableEq G]
    (gates : Finset G) (participants : G → Finset P) (root : G → P)
    (hroot : ∀ g ∈ gates, root g ∈ participants g)
    (Label : G → Type) [∀ g, Fintype (Label g)] (k : ℕ)
    (c : (g : G) → Label g → ℂ) {Out In : P → Type}
    (T : (p : P) → DistributedOperatorContraction.GateLabelsAt gates participants Label p →
      (DistributedOperatorContraction.SampleAt gates participants p → Fin k) →
        Matrix (Out p) (In p) ℂ) (p₀ : P) (μ : ℂ) :
    DistributedOperatorContraction.contractedOperator gates participants root hroot Label k c
      (fun p ξ j ↦ (if p = p₀ then μ else 1) • T p ξ j) =
      μ • DistributedOperatorContraction.contractedOperator
        gates participants root hroot Label k c T := by
  classical
  rw [DistributedOperatorContraction.contractedOperator_eq_sum_productMatrix,
    DistributedOperatorContraction.contractedOperator_eq_sum_productMatrix]
  simp_rw [TNLean.PEPS.PairEffect.partyProductMatrix_smul_at_party]
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro ξ _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

end TNLean.PEPS.Approximation.DistributedOperatorContraction
