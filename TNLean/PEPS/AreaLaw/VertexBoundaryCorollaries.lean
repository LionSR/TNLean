/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryConventions
import TNLean.PEPS.AreaLaw.TheoremStatements

/-!
# Vertex-boundary consequences of an edge-boundary area law

An edge-boundary entropy bound with a nonnegative constant implies the
inner-boundary and endpoint-boundary formulations, with factors four and two.
The uniform consequence keeps the constant independent of the domain,
interaction family, ground vector, and cut. The edge-boundary area law is
an explicit hypothesis; this module does not prove that theorem.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Corollary 1.2 (`cor:rectangles`),
  `00-introduction.tex`, lines 59–85, at source revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/sections/00-introduction.tex
Labels: cor:rectangles.
independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8759-tnlean.peps.arealaw.regionalentropy_le_four_mul_innerboundary_card
Downstream declaration: TNLean.PEPS.AreaLaw.regionalEntropy_le_four_mul_innerBoundary_card
Provenance-ID: 8759-tnlean.peps.arealaw.regionalentropy_le_two_mul_endpointboundary_card
Downstream declaration: TNLean.PEPS.AreaLaw.regionalEntropy_le_two_mul_endpointBoundary_card
Provenance-ID: 8759-tnlean.peps.arealaw.uniformarealaw.vertex_boundary_bounds
Downstream declaration: TNLean.PEPS.AreaLaw.UniformAreaLaw.vertex_boundary_bounds
-/

namespace TNLean.PEPS.AreaLaw

/-- The inner-boundary formulation follows from the edge-boundary inequality.
Source: area-law Corollary 1.2, first displayed entropy bound.
The edge-boundary inequality is an explicit hypothesis. -/
theorem regionalEntropy_le_four_mul_innerBoundary_card
    {Λ : Finset (ℤ × ℤ)} {q : ℕ} {Ω : StateSpace Λ q} {A : Finset (Site Λ)}
    {C : ℝ} (hC : 0 ≤ C)
    (harea : regionalEntropy Λ q Ω A ≤ C * (edgeBoundary Λ A).card) :
    regionalEntropy Λ q Ω A ≤ 4 * C * (innerBoundary Λ A).card := by
  have hcard : ((edgeBoundary Λ A).card : ℝ) ≤ 4 * (innerBoundary Λ A).card :=
    by exact_mod_cast edgeBoundary_card_le_four_mul_innerBoundary_card Λ A
  calc
    _ ≤ C * (edgeBoundary Λ A).card := harea
    _ ≤ C * (4 * (innerBoundary Λ A).card) := mul_le_mul_of_nonneg_left hcard hC
    _ = 4 * C * (innerBoundary Λ A).card := by ring

/-- The endpoint-boundary formulation follows from the edge-boundary inequality.
Source: area-law Corollary 1.2, second displayed entropy bound.
The edge-boundary inequality is an explicit hypothesis. -/
theorem regionalEntropy_le_two_mul_endpointBoundary_card
    {Λ : Finset (ℤ × ℤ)} {q : ℕ} {Ω : StateSpace Λ q} {A : Finset (Site Λ)}
    {C : ℝ} (hC : 0 ≤ C)
    (harea : regionalEntropy Λ q Ω A ≤ C * (edgeBoundary Λ A).card) :
    regionalEntropy Λ q Ω A ≤ 2 * C * (endpointBoundary Λ A).card := by
  have hcard : ((edgeBoundary Λ A).card : ℝ) ≤ 2 * (endpointBoundary Λ A).card :=
    by exact_mod_cast edgeBoundary_card_le_two_mul_endpointBoundary_card Λ A
  calc
    _ ≤ C * (edgeBoundary Λ A).card := harea
    _ ≤ C * (2 * (endpointBoundary Λ A).card) := mul_le_mul_of_nonneg_left hcard hC
    _ = 2 * C * (endpointBoundary Λ A).card := by ring

/-- A uniform edge-boundary area law implies both uniform vertex-boundary bounds.
Source: area-law Corollary 1.2. The area-law theorem is an explicit hypothesis,
and the same constant is chosen before all physical instances and cuts. -/
theorem UniformAreaLaw.vertex_boundary_bounds (h : UniformAreaLaw) :
    ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J,
          ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
            IsGappedGroundState Λ q H.operator E₀ Ω Δ →
              ∀ A : Finset (Site Λ),
                regionalEntropy Λ q Ω A ≤ 4 * C * (innerBoundary Λ A).card ∧
                regionalEntropy Λ q Ω A ≤ 2 * C * (endpointBoundary Λ A).card := by
  intro q hq R J Δ hJ hΔ
  obtain ⟨C, hC, harea⟩ := h q hq R J Δ hJ hΔ
  exact ⟨C, hC, fun Λ H E₀ Ω hgap A ↦
    ⟨regionalEntropy_le_four_mul_innerBoundary_card hC (harea Λ H E₀ Ω hgap A),
      regionalEntropy_le_two_mul_endpointBoundary_card hC (harea Λ H E₀ Ω hgap A)⟩⟩

end TNLean.PEPS.AreaLaw
