/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairCurrentDisjointness
import TNLean.PEPS.AreaLaw.Geometry.RepairCurrentTerminalDisjointness
import TNLean.PEPS.AreaLaw.Geometry.RepairFinalRegionStabilization
import TNLean.PEPS.AreaLaw.Geometry.RepairLatticeCoverage
import TNLean.PEPS.AreaLaw.Geometry.RepairTerminalInteriors

/-!
# Exclusive final lattice coverage at an empty generation

At a generation without remaining marks, every current region avoids the
original accumulated terminal interiors. The final regions equal these
current regions. At the prescribed origin, every lattice point therefore
belongs either to the terminal interiors or to exactly one final region.
The identifier family includes the retained dummy.

The generation is supplied as part of the hypotheses. The metric hypotheses
suffice for terminal avoidance; the lower stopping-scale and positive-boundary
conditions are used only for lattice coverage at the prescribed origin.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 398–417;
`geometry:repair-induction`, lines 474–478 and 526–541; final lattice regions,
lines 545–561; and terminal exceptional sites, lines 694–707.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

namespace RepairMetricHypotheses

section ArbitraryOrigin

variable {o : ℝ × ℝ} {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
  {C k₀ : ℕ} {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar : ℝ}

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

variable {a₀ : ℝ} (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A)
  (C := C) (k₀ := k₀) (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)

include h

/-- At an empty generation, every actual current region avoids the original
accumulated terminal interiors.
Source: area-law Section 11, lines 398–417; `geometry:repair-induction`,
lines 474–478 and 526–541; and final regions, lines 558–561. -/
theorem current_disjoint_terminalInteriors_of_isEmpty (N : ℕ)
    [IsEmpty (𝔇 N).markIndex] (i : (𝔇 N).regionIndex) :
    Disjoint ((𝔇 N).current i)
      (repairTerminalInteriors o Λ A C k₀ hC h₀ Sstar) := by
  refine (h.current_disjoint_earlierTerminalSquares N i).mono_right ?_
  rw [repairTerminalInteriors_eq_iUnion_lt_of_isEmpty o Λ A C k₀ hC h₀ Sstar N]
  exact Set.iUnion_mono fun _ ↦ Set.iUnion_mono fun _ ↦
    Set.iUnion_mono fun _ ↦ interior_subset

end ArbitraryOrigin

section PrescribedOrigin

variable {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
  {C k₀ : ℕ} {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar : ℝ}

local notation "𝔇" => repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar

variable {a₀ : ℝ} (h : RepairMetricHypotheses (o := dyadicOrigin) (Λ := Λ) (A := A)
  (C := C) (k₀ := k₀) (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)

include h

/-- Each lattice point belongs either to the original terminal interiors and
to no final region, or to exactly one final region and not to the terminal
interiors. All actual identifiers at the supplied empty generation are used,
including the dummy.
Source: area-law Section 11, positive-boundary convention, lines 102–105;
replacement instructions, lines 398–417; and lattice partition, lines 545–561. -/
theorem lattice_mem_terminal_or_unique_final_of_isEmpty
    (hSstar : 1 ≤ Sstar) (hboundary : 0 < (edgeBoundary Λ A).card)
    (N : ℕ) [IsEmpty (𝔇 N).markIndex] (z : ℤ × ℤ) :
    (integerPoint z ∈ repairTerminalInteriors dyadicOrigin Λ A C k₀ hC h₀ Sstar ∧
      ∀ i : (𝔇 N).regionIndex,
        integerPoint z ∉ repairFinalRegion dyadicOrigin Λ A C k₀ hC h₀ Sstar N i) ∨
    (integerPoint z ∉ repairTerminalInteriors dyadicOrigin Λ A C k₀ hC h₀ Sstar ∧
      ∃! i : (𝔇 N).regionIndex,
        integerPoint z ∈ repairFinalRegion dyadicOrigin Λ A C k₀ hC h₀ Sstar N i) := by
  classical
  simp only [repairFinalRegion_eq_current_of_isEmpty]
  by_cases hz : integerPoint z ∈
      repairTerminalInteriors dyadicOrigin Λ A C k₀ hC h₀ Sstar
  · exact Or.inl ⟨hz, fun i hi ↦
      Set.disjoint_left.mp (h.current_disjoint_terminalInteriors_of_isEmpty N i) hi hz⟩
  · rcases h.lattice_mem_current_or_terminal_before hSstar hboundary N z with
      ⟨i, hi⟩ | ⟨t, _, htz⟩
    · refine Or.inr ⟨hz, i, hi, ?_⟩
      intro k hk
      by_contra hki
      exact Set.disjoint_left.mp (h.current_pairwise_disjoint N hki) hk hi
    · exact (hz (Set.mem_iUnion.mpr ⟨t, htz⟩)).elim

end PrescribedOrigin

end RepairMetricHypotheses

end TNLean.PEPS.AreaLaw.Geometry
