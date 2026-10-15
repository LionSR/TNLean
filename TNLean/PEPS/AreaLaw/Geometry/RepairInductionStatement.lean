/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.IsolatedStars
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendants

/-!
# The statement of the uniform repair induction

For the repair stages with stopping scale `S_*`, the uniform repair induction
asserts, at one constant `a₀` for all generations: isolated stars and the
separation inequality at every generation, avoidance of the closed
terminal squares of earlier generations, disjoint simultaneous removal
squares, same-label contacts of each replacement only at marks of the next
generation, confinement of descendants to sup distance `2 d(S)`, and finite
termination of each branch.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417, and
`geometry:repair-induction`, lines 471–485.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

section Stages

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
  (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

/-- The conclusion of the uniform repair induction for the actual repair stages
with stopping scale `S_*` and isolation constant `a₀`, the same at every
generation.
Source: area-law Section 11, `geometry:repair-induction`, lines 471–485. -/
structure IsUniformRepairInduction (a₀ : ℝ) : Prop where
  /-- Every generation has isolated stars, with the separation inequality.
  Source: area-law Section 11, lines 473–478. -/
  hasIsolatedStars : ∀ j, (repairStage o Λ A C k₀ hC h₀ Sstar j).HasIsolatedStars a₀
  /-- Every star avoids the closed terminal squares of earlier generations.
  Source: area-law Section 11, lines 474–476 and 526–536. -/
  disjoint_terminal : ∀ j p,
    Disjoint (Metric.closedBall ((repairStage o Λ A C k₀ hC h₀ Sstar j).location p)
      (a₀ * (repairStage o Λ A C k₀ hC h₀ Sstar j).scale p))
      (repairEarlierTerminalSquares o Λ A C k₀ hC h₀ Sstar j)
  /-- The simultaneous removal squares of one generation are disjoint.
  Source: area-law Section 11, line 478. -/
  disjoint_repairSquare : ∀ j p q, p ≠ q →
    Disjoint (repairSquare ((repairStage o Λ A C k₀ hC h₀ Sstar j).location p)
      ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale p))
      (repairSquare ((repairStage o Λ A C k₀ hC h₀ Sstar j).location q)
      ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale q))
  /-- A replacement meets a distinct identifier of the same label only at
  marks of the next generation. Since there are finitely many marks, every
  positive-length interface of a replacement with a distinct identifier joins
  opposite labels.
  Source: area-law Section 11, lines 479–482. -/
  contact_subset_marks : ∀ j x y m, x ≠ y →
    repairRegionParent o Λ A C k₀ hC h₀ Sstar j x = some m →
    (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).color x =
      (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).color y →
    closure ((repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).current x) ∩
      closure ((repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).current y) ⊆
      Set.range (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).location
  /-- Every descendant mark of `(v, S)` lies within sup distance `2 d(S)` of `v`.
  Source: area-law Section 11, lines 482–484. -/
  dist_descendant_le : ∀ i n q,
    dist ((repairStage o Λ A C k₀ hC h₀ Sstar (i + n)).location q)
      ((repairStage o Λ A C k₀ hC h₀ Sstar i).location
        (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q)) ≤
      2 * repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar i).scale
        (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q))
  /-- Every descendant birth region of `(v, S)` lies within sup distance
  `2 d(S)` of `v`.
  Source: area-law Section 11, lines 482–484. -/
  birth_descendant_subset : ∀ i n x m,
    repairRegionParent o Λ A C k₀ hC h₀ Sstar (i + n) x = some m →
    (repairStage o Λ A C k₀ hC h₀ Sstar (i + n + 1)).birth x ⊆
      Metric.closedBall ((repairStage o Λ A C k₀ hC h₀ Sstar i).location
        (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n m))
        (2 * repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar i).scale
          (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n m)))
  /-- Each branch terminates after finitely many generations.
  Source: area-law Section 11, line 484. -/
  terminates : ∀ i p, ∃ n, ∀ q, repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q ≠ p

end Stages

/-- The statement of the uniform repair induction: for a sufficiently small
fixed `a₀` and every sufficiently large stopping scale `S_*`, and for every
fixed layer width and every sufficiently large lower layer index, the actual
repair stages satisfy the uniform repair induction with constant `a₀`.
Source: area-law Section 11, `geometry:repair-induction`, lines 471–485, with
the choice of `S_*` and `k₀` in lines 380–394. -/
def UniformRepairInductionStatement : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
    ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
      (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
        IsUniformRepairInduction o Λ A C k₀ hC h₀ Sstar a₀

end TNLean.PEPS.AreaLaw.Geometry
