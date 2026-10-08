/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ConditionalTwoFamilies
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Labelled conditional-family regressions with nonempty external systems. -/

open scoped BigOperators
open TNLean.PEPS.AreaLaw
open TNLean.PEPS.AreaLaw.Geometry

/-- A common order intermixes the family labels, with a nonempty remainder. -/
abbrev conditionalPartition : OrderedTwoFamilyPartition ({0, 1, 2, 3} : Finset (Fin 6)) where
  pieceCount := 3
  family := ![1, 0, 0]
  piece := ![{3}, {2}, {0}]
  residual := {1}
  disjoint := by decide
  residual_disjoint := by decide
  cover := by decide

example : conditionalPartition.earlierSameFamily (2 : Fin 3) = {2} := by decide

example (ψ : EuclideanSpace ℂ (Fin 6 → Fin 2)) (hψ : ‖ψ‖ = 1)
    (ε : Fin 3 → ℝ)
    (h₀ : FiniteProduct.mutualInformation (fun _ : Fin 6 ↦ Fin 2) ψ {3} {5} ≤ ε 0)
    (h₁ : FiniteProduct.mutualInformation (fun _ : Fin 6 ↦ Fin 2) ψ {2} {4, 5} ≤ ε 1)
    (h₂ : FiniteProduct.mutualInformation (fun _ : Fin 6 ↦ Fin 2) ψ {0} {2, 4, 5} ≤ ε 2) :
    FiniteProduct.conditionalMutualInformation (fun _ : Fin 6 ↦ Fin 2)
        ψ {0, 1, 2, 3} {5} {4} ≤
      2 * FiniteProduct.entropy (fun _ : Fin 6 ↦ Fin 2) ψ {1} + ∑ i, ε i := by
  apply conditionalPartition.conditionalMutualInformation_le_sum
    (fun _ : Fin 6 ↦ Fin 2) ψ hψ {4} {5} (by decide) (by decide) (by decide) ε
  · intro i hi
    fin_cases i
    · norm_num [conditionalPartition] at hi
    · have hR : ({5} : Finset (Fin 6)) ∪ {4} ∪
          conditionalPartition.earlierSameFamily (1 : Fin 3) = {4, 5} := by decide
      change FiniteProduct.mutualInformation _ ψ {2}
        ({5} ∪ {4} ∪ conditionalPartition.earlierSameFamily (1 : Fin 3)) ≤ ε 1
      rw [hR]
      exact h₁
    · have hR : ({5} : Finset (Fin 6)) ∪ {4} ∪
          conditionalPartition.earlierSameFamily (2 : Fin 3) = {2, 4, 5} := by decide
      change FiniteProduct.mutualInformation _ ψ {0}
        ({5} ∪ {4} ∪ conditionalPartition.earlierSameFamily (2 : Fin 3)) ≤ ε 2
      rw [hR]
      exact h₂
  · intro i hi
    fin_cases i
    · have hR : (({0, 1, 2, 3} : Finset (Fin 6)) ∪ {4})ᶜ ∪
          conditionalPartition.earlierSameFamily (0 : Fin 3) = {5} := by decide
      change FiniteProduct.mutualInformation _ ψ {3}
        (({0, 1, 2, 3} ∪ {4})ᶜ ∪ conditionalPartition.earlierSameFamily (0 : Fin 3)) ≤ ε 0
      rw [hR]
      exact h₀
    · norm_num [conditionalPartition] at hi
    · norm_num [conditionalPartition] at hi

-- The native result uses existing regional entropy, with no new CMI definition.
example (Λ : Finset (ℤ × ℤ)) (q : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (G B C : Finset (Site Λ)) (P : OrderedTwoFamilyPartition G)
    (hGB : Disjoint G B) (hGC : Disjoint G C) (hBC : Disjoint B C)
    (ε : Fin P.pieceCount → ℝ)
    (h₀ : ∀ i, P.family i = 0 →
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (P.piece i)
        (C ∪ B ∪ P.earlierSameFamily i) ≤ ε i)
    (h₁ : ∀ i, P.family i = 1 →
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (P.piece i)
        ((G ∪ B)ᶜ ∪ P.earlierSameFamily i) ≤ ε i) :
    regionalEntropy Λ q Ω (G ∪ B) + regionalEntropy Λ q Ω (C ∪ B) -
        regionalEntropy Λ q Ω B - regionalEntropy Λ q Ω (G ∪ C ∪ B) ≤
      2 * regionalEntropy Λ q Ω P.residual + ∑ i, ε i :=
  regionalEntropy_conditional_le_residual_add_sum Λ q Ω hΩ G B C P hGB hGC hBC ε h₀ h₁

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition.conditionalMutualInformation_le_sum'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition.conditionalMutualInformation_le_sum

/--
info: 'TNLean.PEPS.AreaLaw.regionalEntropy_conditional_le_residual_add_sum'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.AreaLaw.regionalEntropy_conditional_le_residual_add_sum
