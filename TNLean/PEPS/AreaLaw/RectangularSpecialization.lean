/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.RectangleInteraction
import QICLean.ManyBody.Sites.Lattice.Rectangle
import TNLean.PEPS.AreaLaw.RegionalStates.Regions.TheoremStatements
import QICLean.ManyBody.Entropy.PlaneBoundaryEntropy
import TNLean.PEPS.AreaLaw.SquareAreaLawSpecialization
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Entropy area law on arbitrary native rectangles from the uniform area law

The uniform finite-domain area law is the sole analytic hypothesis. The
constant is chosen before both side lengths, the native site and edge terms,
the ground vector, and the cut. The conclusion uses native configuration
entropy and the actual native edge and vertex boundaries, for every `q ≥ 1`.
Zero sides, one-site rectangles, strips, and empty boundaries are included.

The implication `UniformAreaLaw.rectangularEntropyAreaLaw` takes the uniform
finite-domain area law as its premise. The unconditional Corollary 1.2 for
rectangles is `rectangularEntropyAreaLaw` in
`TNLean.PEPS.AreaLaw.AreaLawTheorem`, which discharges that premise with
`uniformAreaLaw`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Theorem 1.1 and Corollary 1.2 (`cor:rectangles`), and
*Polynomial PEPS approximation of gapped square-grid ground states*,
Proposition 2.1, at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

open ManyBody (RectangleStateSpace rectangleAreaLawState
  regionEntropy_le_four_mul_innerBoundary_card regionEntropy_le_two_mul_endpointBoundary_card)

open ManyBody (Edge RectangleInteraction SquareLatticeVertex squareLatticeGraph)

open scoped Matrix.Norms.L2Operator

noncomputable section

open ManyBody (IsGapped groundSpace rectangularDomain rectangleSiteEquiv)

open ManyBody (innerBoundary endpointBoundary)

namespace TNLean.PEPS.AreaLaw

/-- Native rectangular entropy, with one constant for the edge and both
vertex-boundary forms. Source: Corollary 1.2. This proposition states the
conclusion; `rectangularEntropyAreaLaw` proves it. -/
def RectangularEntropyAreaLaw : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ width height : ℕ, ∀ h : RectangleInteraction width height q,
        h.hamiltonian.IsHermitian → (∀ i, ‖h.term i‖ ≤ J) →
        ∀ E₀ : ℝ, ∀ Ω : RectangleStateSpace width height q,
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
          ∀ A : Finset (SquareLatticeVertex width height),
            ManyBody.regionEntropy Ω A ≤
              C * Fintype.card
                {e : Edge (squareLatticeGraph width height) // ManyBody.IsRegionBoundaryEdge A e} ∧
            ManyBody.regionEntropy Ω A ≤
              4 * C * (innerBoundary (squareLatticeGraph width height) A).card ∧
            ManyBody.regionEntropy Ω A ≤
              2 * C * (endpointBoundary (squareLatticeGraph width height) A).card

/-- The original regional entropy is exactly the transported domain entropy.
Source: Corollary 1.2, relabeling the same tensor factors. -/
theorem regionEntropy_rectangleAreaLawState {width height q : ℕ}
    (Ω : RectangleStateSpace width height q) (A : Finset (SquareLatticeVertex width height)) :
    ManyBody.regionEntropy (rectangleAreaLawState Ω)
        (A.map (rectangleSiteEquiv width height).toEmbedding) =
      ManyBody.regionEntropy Ω A := by
  exact Approximation.finiteProductEntropy_relabel (rectangleSiteEquiv width height) q Ω A

/-- The finite-domain area law implies all three native rectangular bounds
with the same constant. Only the term-norm, total-Hermiticity and full-system gap
hypotheses enter the physical instance, beyond the supports that the interaction carries. Source:
the implication
from Theorem 1.1 to Corollary 1.2. Theorem 1.1 is an explicit hypothesis. -/
theorem UniformAreaLaw.rectangularEntropyAreaLaw (harea : UniformAreaLaw) :
    RectangularEntropyAreaLaw := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, hC, hbound⟩ := harea q hq 1 J Δ hJ hΔ
  refine ⟨C, hC, fun width height h hH hΦ E₀ Ω hΩ hgap hspan A ↦ ?_⟩
  obtain ⟨hΩ', hgap', hspan'⟩ := h.isGapped_toPlaneInteraction_hermitianPart hH hΩ hgap hspan
  have h := hbound (rectangularDomain width height)
    (ManyBody.RectangleInteraction.toPlaneInteraction h.hermitianPart)
    h.isHermitian_toPlaneInteraction_hermitianPart_term
    (h.norm_toPlaneInteraction_hermitianPart_term_le hΦ) E₀
    (rectangleAreaLawState Ω) hΩ' hgap' hspan' (A.map (rectangleSiteEquiv width height).toEmbedding)
  have hi := regionEntropy_le_four_mul_innerBoundary_card hC h
  have he := regionEntropy_le_two_mul_endpointBoundary_card hC h
  rw [regionEntropy_rectangleAreaLawState, ManyBody.card_edgeBoundary_rectangular] at h
  rw [regionEntropy_rectangleAreaLawState, ManyBody.card_innerBoundary_rectangular] at hi
  rw [regionEntropy_rectangleAreaLawState, ManyBody.card_endpointBoundary_rectangular] at he
  exact ⟨h, hi, he⟩

/-- The rectangular result supplies the accepted square statement, the equal-side case,
without changing its `q ≥ 2` signature. Source: polynomial-PEPS Proposition 2.1.
The rectangular area law is an explicit hypothesis. -/
theorem RectangularEntropyAreaLaw.squareEntropyAreaLaw (harea : RectangularEntropyAreaLaw) :
    Approximation.SquareEntropyAreaLaw := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, hC, hbound⟩ := harea q (by omega) J Δ hJ hΔ
  exact ⟨C, hC, fun L Ω ⟨h, hH, hΦ, E₀, hΩ, hgap, hspan⟩ A ↦
    (hbound L L h hH hΦ E₀ Ω hΩ hgap hspan A).1⟩

end TNLean.PEPS.AreaLaw
