/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairFinalRegionStabilization
import TNLean.PEPS.AreaLaw.Geometry.RepairLatticeCoverage

/-!
# Final-region coverage at an empty generation

If an actual generation has no remaining repair marks, every integer lattice
point lies in one of that generation's final regions or in the union of the
terminal-square interiors. The assertion is conditional on the given empty
generation and does not assert uniqueness or termination.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417,
and the lattice partition argument, lines 545–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {C k₀ : ℕ}
  {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar : ℝ}

local notation "𝔇" => repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar

namespace RepairMetricHypotheses

/-- At a given empty generation, every lattice point lies in a final region
or in the original aggregate of terminal-square interiors.
Source: area-law Section 11, lines 393–417 and 545–561; the positive-boundary
assumption of Proposition two-families is at lines 102–105. -/
theorem lattice_mem_final_or_terminal_of_isEmpty {a₀ : ℝ}
    (h : RepairMetricHypotheses (o := dyadicOrigin) (Λ := Λ) (A := A)
      (C := C) (k₀ := k₀) (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)
    (hSstar : 1 ≤ Sstar) (hboundary : 0 < (edgeBoundary Λ A).card)
    (N : ℕ) (hEmpty : IsEmpty (𝔇 N).markIndex) (z : ℤ × ℤ) :
    (∃ i : (𝔇 N).regionIndex,
      integerPoint z ∈ repairFinalRegion dyadicOrigin Λ A C k₀ hC h₀ Sstar N i) ∨
      integerPoint z ∈ repairTerminalInteriors dyadicOrigin Λ A C k₀ hC h₀ Sstar := by
  classical
  let := hEmpty
  rcases h.lattice_mem_current_or_terminal_before hSstar hboundary N z with
    ⟨i, hi⟩ | ⟨t, ht, hz⟩
  · exact Or.inl ⟨i, (repairFinalRegion_eq_current_of_isEmpty
      dyadicOrigin Λ A C k₀ hC h₀ Sstar N i).symm ▸ hi⟩
  · exact Or.inr (Set.mem_iUnion.mpr ⟨t, hz⟩)

end RepairMetricHypotheses

end TNLean.PEPS.AreaLaw.Geometry
