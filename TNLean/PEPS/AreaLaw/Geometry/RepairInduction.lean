/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStageStars
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionStatement

/-!
# The uniform repair induction from the initial isolated stars

The statement of the initial isolated-star lemma implies the statement of the
uniform repair induction. Take the isolation constant `a₀` to be the smaller of
the initial constant and `1/4`, and the stopping scale and the lower layer
index so large that the scale margins and the initial scale bound hold. The
initial isolated stars persist for the smaller constant; one repair step turns
isolated stars of one generation into isolated stars of the next, with the same
constant; and the remaining assertions are the metric invariants and the
contact theorem for the actual repair stages.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 332–349, and
`geometry:repair-induction`, lines 471–543.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- **Uniform repair induction**, from the conclusion of the initial
isolated-star lemma.
Source: area-law Section 11, `geometry:repair-induction`, lines 471–543. -/
theorem uniformRepairInductionStatement_of_initialIsolatedStars
    (hinit : InitialIsolatedStarsStatement) : UniformRepairInductionStatement := by
  obtain ⟨a₁, ha₁, hinit⟩ := hinit
  set a₀ := min a₁ (1 / 4)
  have ha₀ : 0 < a₀ := lt_min ha₁ (by norm_num)
  have ha₀' : a₀ ≤ 1 / 4 := min_le_right _ _
  have ha₀₁ : a₀ ≤ a₁ := min_le_left _ _
  obtain ⟨T, hT⟩ := exists_repairMetricHypotheses ha₀ ha₀'
  refine ⟨a₀, ha₀, T, fun Sstar hS C ↦ ?_⟩
  obtain ⟨K₁, hK₁⟩ := hinit C
  obtain ⟨K₂, hK₂⟩ := hT Sstar hS C
  refine ⟨max K₁ K₂, fun o Λ A k₀ hC h₀ hK ↦ ?_⟩
  have hM := hK₂ o Λ A k₀ hC h₀ (le_of_max_le_right hK)
  have hI := hK₁ o Λ A k₀ hC h₀ (le_of_max_le_left hK)
  have hstars : ∀ j (p : (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex),
      IsIsolatedStar (repairStage o Λ A C k₀ hC h₀ Sstar j).current
        (repairStage o Λ A C k₀ hC h₀ Sstar j).color
        ((repairStage o Λ A C k₀ hC h₀ Sstar j).location p)
        (a₀ * (repairStage o Λ A C k₀ hC h₀ Sstar j).scale p) := by
    intro j
    induction j with
    | zero => exact (hI.mono (fun p ↦ hM.scale_pos 0 p) ha₀ ha₀₁).2
    | succ j ih => exact hM.isIsolatedStar_succ ha₀' j ih
  exact
    { hasIsolatedStars := fun j ↦ ⟨hM.separated j, hstars j⟩
      disjoint_terminal := hM.disjoint_earlierTerminalSquares
      disjoint_repairSquare := hM.disjoint_repairSquare
      contact_subset_marks := fun j x y m hxy hpar hcol ↦
        hM.contact_subset_marks j (hstars j) x y m hxy hpar hcol
      dist_descendant_le := hM.dist_descendant_le
      birth_descendant_subset := hM.birth_descendant_subset
      terminates := hM.terminates }

end TNLean.PEPS.AreaLaw.Geometry
