/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStageStars
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionStatement
import TNLean.PEPS.AreaLaw.Geometry.InitialStars

/-!
# The uniform repair induction

The statement of the initial isolated-star lemma implies the statement of the
uniform repair induction; with the initial isolated stars this proves the
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

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- **Uniform repair induction at given data.** If the initial stage has isolated
stars with constant `a₁`, and the repair data satisfy the metric hypotheses with
an isolation constant `a₀ ≤ min a₁ (1/4)`, then the actual repair stages satisfy
the uniform repair induction with constant `a₀`.
Source: area-law Section 11, `geometry:repair-induction`, lines 471–543. -/
theorem isUniformRepairInduction_of_repairMetricHypotheses {o : ℝ × ℝ}
    {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {C k₀ : ℕ} {hC : 2 ≤ C}
    {h₀ : 50000000 ≤ k₀} {Sstar a₀ a₁ : ℝ}
    (hI : (initialRepairStage o Λ A C k₀ hC h₀).HasIsolatedStars a₁)
    (hM : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
      (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)
    (ha₀' : a₀ ≤ 1 / 4) (ha₀₁ : a₀ ≤ a₁) :
    IsUniformRepairInduction o Λ A C k₀ hC h₀ Sstar a₀ := by
  have hstars : ∀ j (p : (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex),
      IsIsolatedStar (repairStage o Λ A C k₀ hC h₀ Sstar j).current
        (repairStage o Λ A C k₀ hC h₀ Sstar j).color
        ((repairStage o Λ A C k₀ hC h₀ Sstar j).location p)
        (a₀ * (repairStage o Λ A C k₀ hC h₀ Sstar j).scale p) := by
    intro j
    induction j with
    | zero => exact (hI.mono (fun p ↦ hM.scale_pos 0 p) hM.pos ha₀₁).2
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

/-- **Uniform repair induction with explicit thresholds.** With isolation
constant `1/128`, every stopping scale `S_* ≥ repairMarginThreshold (1/128)`
and every lower layer index `k₀ ≥ fineScaleIndexThreshold S_*`, the actual
repair stages satisfy the uniform repair induction, for every width.
Source: area-law Section 11, `geometry:initial-stars`, lines 332–349, and
`geometry:repair-induction`, lines 471–543. -/
theorem isUniformRepairInduction_of_le {Sstar : ℝ}
    (hS : repairMarginThreshold (1 / 128) ≤ Sstar) (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hK : fineScaleIndexThreshold Sstar ≤ k₀) :
    IsUniformRepairInduction o Λ A C k₀ hC h₀ Sstar (1 / 128) :=
  isUniformRepairInduction_of_repairMetricHypotheses
    (initialRepairStage_hasIsolatedStars o Λ A C k₀ hC h₀)
    (repairMetricHypotheses_of_le (by norm_num) (by norm_num) hS o Λ A C k₀ hC h₀ hK)
    (by norm_num) le_rfl

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
  exact ⟨max K₁ K₂, fun o Λ A k₀ hC h₀ hK ↦
    isUniformRepairInduction_of_repairMetricHypotheses
      (hK₁ o Λ A k₀ hC h₀ (le_of_max_le_left hK))
      (hK₂ o Λ A k₀ hC h₀ (le_of_max_le_right hK)) ha₀' ha₀₁⟩

/-- **Uniform repair induction** (Lemma 11.4). For a sufficiently small fixed
isolation constant and every sufficiently large stopping scale, for every
width and every sufficiently large lower layer index, the actual repair stages
have isolated stars with that constant at every generation, avoid earlier
terminal squares, have disjoint removal squares and same-label contacts only
at marks of the next generation, keep descendants within `2 d(S)`, and
terminate along every branch.
Source: area-law Section 11, `geometry:repair-induction`, lines 471–543. -/
theorem uniformRepairInductionStatement_holds : UniformRepairInductionStatement :=
  uniformRepairInductionStatement_of_initialIsolatedStars initialIsolatedStarsStatement_holds

end TNLean.PEPS.AreaLaw.Geometry
