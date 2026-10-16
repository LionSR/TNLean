/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInteriors
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionMetric
import TNLean.PEPS.AreaLaw.Geometry.RepairNextRegionDisjointness

/-!
# Pairwise disjointness throughout the repair construction

Under the existing metric hypotheses for the repair induction, the current
regions at every actual generation are pairwise disjoint. The initial family
uses the same jointly chosen belt residues as the actual repair construction.
At a successor generation, distinct parent removal squares are disjoint and
each fresh open region lies in its parent's closed removal square. The
one-step disjointness theorem therefore applies to the actual assignments.

This is an auxiliary consequence of the metric hypotheses. It does not assert
coverage, a lattice partition, or the quantitative conclusion of the
two-family proposition.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–177,
212–218 and 299–323; replacement instructions, lines 393–417; and
`geometry:repair-induction`, lines 478 and 486–514.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

variable {o Λ A C k₀ hC h₀ Sstar}

namespace RepairMetricHypotheses

variable {a₀ : ℝ} (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
  (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)

include h

/-- The actual current regions are pairwise disjoint at every generation
under the metric hypotheses of the repair induction.
Source: area-law Section 11, `prop:two-families`, lines 154–177,
212–218 and 299–323; lines 393–417; and `geometry:repair-induction`,
lines 478 and 486–514. -/
theorem current_pairwise_disjoint :
    ∀ j, Pairwise (fun i k : (𝔇 j).regionIndex ↦
      Disjoint ((𝔇 j).current i) ((𝔇 j).current k)) := by
  exact Nat.rec
    (motive := fun j ↦ Pairwise (fun i k : (𝔇 j).regionIndex ↦
      Disjoint ((𝔇 j).current i) ((𝔇 j).current k)))
    (initialOpenRegion_pairwise_disjoint o k₀ (boundaryEndpoints Λ A) C _ _ hC h₀)
    (fun j ih ↦ by
      let : Nonempty (𝔇 j).regionIndex := ⟨(𝔇 j).dummy⟩
      exact repairNextCurrentRegion_pairwise_disjoint j
        (𝔇 j).current (𝔇 j).location (𝔇 j).scale Sstar (𝔇 j).color
        (repairCurrentAssignments (𝔇 j).current (𝔇 j).location (𝔇 j).scale)
        ih (h.disjoint_repairSquare j)
        (fun p H ↦ interior_subset.trans
          (repairReplacementBirthRegion_subset_repairSquare _ _ _ _ H)))

end RepairMetricHypotheses

end TNLean.PEPS.AreaLaw.Geometry
