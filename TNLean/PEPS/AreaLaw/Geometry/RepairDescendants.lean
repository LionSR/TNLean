/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStage

/-!
# Ancestors and descendants in the recursive repair

A mark occurrence of the next generation remembers its parent occurrence, and
a fresh replacement identifier remembers the parent occurrence at which it was
born. Iterating the parent map gives the ancestor of a later mark at an earlier
generation; the descendants of a mark are the marks and fresh births whose
ancestor it is. The closed terminal squares created before a generation are collected
for the avoidance assertion of the repair induction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417, and
`geometry:repair-induction`, lines 471–485 and 526–541.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

section Stages

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
  (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

/-- The parent occurrence of a mark of generation `j + 1`.
Source: area-law Section 11, lines 404–409 and 506–514. -/
def repairMarkParent (j : ℕ) :
    (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).markIndex →
      (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex :=
  fun q ↦ (show RepairNextMarkIndex j (repairStage o Λ A C k₀ hC h₀ Sstar j).scale Sstar
    from q).2.1.val

/-- The ancestor at generation `i` of a mark of generation `i + n`.
Source: area-law Section 11, lines 404–409 and 482–484. -/
def repairMarkAncestor (i : ℕ) : (n : ℕ) →
    (repairStage o Λ A C k₀ hC h₀ Sstar (i + n)).markIndex →
      (repairStage o Λ A C k₀ hC h₀ Sstar i).markIndex
  | 0 => id
  | n + 1 => repairMarkAncestor i n ∘ repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + n)

/-- The parent occurrence of a fresh replacement identifier of generation
`j + 1`; retained old identifiers have none.
Source: area-law Section 11, lines 404–409 and 482–484. -/
def repairRegionParent (j : ℕ) :
    (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).regionIndex →
      Option (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex :=
  fun x ↦ Sum.elim (fun _ ↦ none) (fun q ↦ some q.2.1.val)
    (show RepairRegionIndex j (repairStage o Λ A C k₀ hC h₀ Sstar j).scale Sstar
      (repairStage o Λ A C k₀ hC h₀ Sstar j).color
      (letI : Nonempty (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex :=
        ⟨(repairStage o Λ A C k₀ hC h₀ Sstar j).dummy⟩
       repairCurrentAssignments (repairStage o Λ A C k₀ hC h₀ Sstar j).current
        (repairStage o Λ A C k₀ hC h₀ Sstar j).location
        (repairStage o Λ A C k₀ hC h₀ Sstar j).scale) from x)

/-- The union of the closed terminal squares created before generation `j`.
Source: area-law Section 11, lines 398–402 and 526–536. -/
def repairEarlierTerminalSquares (j : ℕ) : Set (ℝ × ℝ) :=
  ⋃ i < j, ⋃ p : {p : (repairStage o Λ A C k₀ hC h₀ Sstar i).markIndex //
      repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar i).scale p) < Sstar},
    repairSquare ((repairStage o Λ A C k₀ hC h₀ Sstar i).location p.val)
      ((repairStage o Λ A C k₀ hC h₀ Sstar i).scale p.val)

end Stages

end TNLean.PEPS.AreaLaw.Geometry
