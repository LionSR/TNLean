/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TwoFamilies
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Integration regressions for the common ordered, family-labelled partition. -/

open scoped BigOperators
open TNLean.PEPS.AreaLaw
open TNLean.PEPS.AreaLaw.Geometry

/-- Three singleton pieces with labels in the shuffled order 1, 0, 1. -/
abbrev shuffledPartition : OrderedTwoFamilyPartition ({0, 1, 2} : Finset (Fin 4)) where
  pieceCount := 3
  family := ![1, 0, 1]
  piece := ![{0}, {1}, {2}]
  residual := ∅
  disjoint := by decide
  residual_disjoint := by decide
  cover := by decide

example : shuffledPartition.earlierSameFamily (0 : Fin 3) = ∅ := by decide
example : shuffledPartition.earlierSameFamily (1 : Fin 3) = ∅ := by decide
example : shuffledPartition.earlierSameFamily (2 : Fin 3) = {0} := by decide

example (ψ : EuclideanSpace ℂ (Fin 4 → Fin 2)) (hψ : ‖ψ‖ = 1)
    (ε : Fin 3 → ℝ)
    (h₀ : FiniteProduct.mutualInformation (fun _ : Fin 4 ↦ Fin 2) ψ {0} {3} ≤ ε 0)
    (h₁ : FiniteProduct.mutualInformation (fun _ : Fin 4 ↦ Fin 2) ψ {1} {3} ≤ ε 1)
    (h₂ : FiniteProduct.mutualInformation (fun _ : Fin 4 ↦ Fin 2) ψ {2} {0, 3} ≤ ε 2) :
    FiniteProduct.entropy (fun _ : Fin 4 ↦ Fin 2) ψ {0, 1, 2} ≤
      (1 / 2) * (ε 0 + ε 1 + ε 2) := by
  have h := shuffledPartition.entropy_le_residual_add_half_sum
    (fun _ : Fin 4 ↦ Fin 2) ψ hψ ε (by
      intro i
      fin_cases i
      · have hR : ({0, 1, 2} : Finset (Fin 4))ᶜ ∪
            shuffledPartition.earlierSameFamily (0 : Fin 3) = {3} := by decide
        change FiniteProduct.mutualInformation _ ψ {0}
          (({0, 1, 2} : Finset (Fin 4))ᶜ ∪
            shuffledPartition.earlierSameFamily (0 : Fin 3)) ≤ ε 0
        rw [hR]
        exact h₀
      · have hR : ({0, 1, 2} : Finset (Fin 4))ᶜ ∪
            shuffledPartition.earlierSameFamily (1 : Fin 3) = {3} := by decide
        change FiniteProduct.mutualInformation _ ψ {1}
          (({0, 1, 2} : Finset (Fin 4))ᶜ ∪
            shuffledPartition.earlierSameFamily (1 : Fin 3)) ≤ ε 1
        rw [hR]
        exact h₁
      · have hR : ({0, 1, 2} : Finset (Fin 4))ᶜ ∪
            shuffledPartition.earlierSameFamily (2 : Fin 3) = {0, 3} := by decide
        change FiniteProduct.mutualInformation _ ψ {2}
          (({0, 1, 2} : Finset (Fin 4))ᶜ ∪
            shuffledPartition.earlierSameFamily (2 : Fin 3)) ≤ ε 2
        rw [hR]
        exact h₂)
  change FiniteProduct.entropy (fun _ : Fin 4 ↦ Fin 2) ψ {0, 1, 2} ≤
    FiniteProduct.entropy (fun _ : Fin 4 ↦ Fin 2) ψ ∅ + (1 / 2) * ∑ i : Fin 3, ε i at h
  simpa [FiniteProduct.entropy_empty _ ψ hψ, Fin.sum_univ_succ, add_assoc] using h

/-- The model-defined regional entropy itself is transported, not replaced by
an unrelated entropy function. -/
example (Λ : Finset (ℤ × ℤ)) (q : ℕ) (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    regionalEntropy Λ q Ω A = FiniteProduct.entropy (fun _ : Site Λ ↦ Fin q) Ω A :=
  regionalEntropy_eq_finiteProduct Λ q Ω A

/--
info: 'TNLean.PEPS.AreaLaw.reducedState_eq_finiteProduct' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.reducedState_eq_finiteProduct

/--
info: 'TNLean.PEPS.AreaLaw.regionalEntropy_eq_finiteProduct' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.regionalEntropy_eq_finiteProduct

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition.entropy_le_residual_add_half_sum'
depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition.entropy_le_residual_add_half_sum

/--
info: 'TNLean.PEPS.AreaLaw.regionalEntropy_le_residual_add_half_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.regionalEntropy_le_residual_add_half_sum
