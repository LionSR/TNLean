/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularHamiltonian
import TNLean.PEPS.AreaLaw.RectangularBoundary
import TNLean.PEPS.AreaLaw.VertexBoundaryCorollaries
import TNLean.PEPS.Approximation.SquareAreaLawSpecialization

/-!
# Conditional entropy area law on arbitrary native rectangles

The uniform finite-domain area law is the sole analytic hypothesis. The
constant is chosen before both side lengths, the native site and edge terms,
the ground vector, and the cut. The conclusion uses native configuration
entropy and the actual native edge and vertex boundaries, for every `q ≥ 1`.
Zero sides, one-site rectangles, strips, and empty boundaries are included.

**Scope restriction (conditional area law):** The implication
`UniformAreaLaw.rectangularEntropyAreaLaw` retains the uniform finite-domain
area law as an explicit, substantive premise. It proves the reduction and does
not assert the unconditional Corollary 1.2. This restriction is documented in
`docs/paper-gaps/arealaw2d_rectangular_specialization_scope.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Theorem 1.1 and Corollary 1.2 (`cor:rectangles`), and
*Polynomial PEPS approximation of gapped square-grid ground states*,
Proposition 2.1, at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw

/-- Native rectangular entropy, with one constant for the edge and both
vertex-boundary forms. Source: Corollary 1.2. This is a proposition specifying
the conclusion, not a proof of the unconditional source corollary. -/
def RectangularEntropyAreaLaw : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ width height : ℕ, ∀ h : RectangularHamiltonian width height q J,
        ∀ E₀ : ℝ, ∀ Ω : RectangleStateSpace width height q,
          h.IsGappedGroundState E₀ Ω Δ → ∀ A : Finset (SquareLatticeVertex width height),
            FiniteProduct.entropy (fun _ : SquareLatticeVertex width height ↦ Fin q) Ω A ≤
              C * Fintype.card
                {e : Edge (squareLatticeGraph width height) // IsRegionBoundaryEdge A e} ∧
            FiniteProduct.entropy (fun _ : SquareLatticeVertex width height ↦ Fin q) Ω A ≤
              4 * C * (rectangleInnerBoundary A).card ∧
            FiniteProduct.entropy (fun _ : SquareLatticeVertex width height ↦ Fin q) Ω A ≤
              2 * C * (rectangleEndpointBoundary A).card

/-- The original regional entropy is exactly the transported domain entropy.
Source: Corollary 1.2, relabeling the same tensor factors. -/
theorem regionalEntropy_rectangleAreaLawState {width height q : ℕ}
    (Ω : RectangleStateSpace width height q) (A : Finset (SquareLatticeVertex width height)) :
    regionalEntropy (rectangularDomain width height) q (rectangleAreaLawState Ω)
        (A.map (rectangleSiteEquiv width height).toEmbedding) =
      FiniteProduct.entropy (fun _ : SquareLatticeVertex width height ↦ Fin q) Ω A := by
  rw [regionalEntropy_eq_finiteProduct]
  exact Approximation.finiteProductEntropy_relabel (rectangleSiteEquiv width height) q Ω A

/-- The finite-domain area law implies all three native rectangular bounds
with the same constant. Only source support, term-norm, total-Hermiticity and
full-system gap hypotheses enter the physical instance. Source: the implication
from Theorem 1.1 to Corollary 1.2. Theorem 1.1 is an explicit hypothesis. -/
theorem UniformAreaLaw.rectangularEntropyAreaLaw (harea : UniformAreaLaw) :
    RectangularEntropyAreaLaw := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, hC, hbound⟩ := harea q hq 1 J Δ hJ hΔ
  refine ⟨C, hC, fun width height h E₀ Ω hΩ A ↦ ?_⟩
  have hgap := h.isGappedGroundState_toAreaLawHamiltonian hJ.le hΩ
  have h := hbound (rectangularDomain width height) (h.toAreaLawHamiltonian hJ.le) E₀
    (rectangleAreaLawState Ω) hgap (A.map (rectangleSiteEquiv width height).toEmbedding)
  have hi := regionalEntropy_le_four_mul_innerBoundary_card hC h
  have he := regionalEntropy_le_two_mul_endpointBoundary_card hC h
  rw [regionalEntropy_rectangleAreaLawState, card_edgeBoundary_rectangular] at h
  rw [regionalEntropy_rectangleAreaLawState, card_innerBoundary_rectangular] at hi
  rw [regionalEntropy_rectangleAreaLawState, card_endpointBoundary_rectangular] at he
  exact ⟨h, hi, he⟩

/-- The accepted square model is the equal-side case of the native rectangular
model, with exactly the same operators and source hypotheses.
Source: polynomial-PEPS `eq:model`. -/
def _root_.TNLean.PEPS.Approximation.SquareHamiltonian.toRectangularHamiltonian
    {L q : ℕ} {J : ℝ} (h : Approximation.SquareHamiltonian L q J) :
    RectangularHamiltonian L L q J where
  siteTerm := h.siteTerm
  edgeTerm := h.edgeTerm
  site_supported := h.site_supported
  edge_supported := h.edge_supported
  site_norm_le := h.site_norm_le
  edge_norm_le := h.edge_norm_le
  hermitian := h.hermitian

/-- The rectangular result supplies the accepted square statement without
changing its `q ≥ 2` signature. Source: polynomial-PEPS Proposition 2.1.
The rectangular area law is an explicit hypothesis. -/
theorem RectangularEntropyAreaLaw.squareEntropyAreaLaw (harea : RectangularEntropyAreaLaw) :
    Approximation.SquareEntropyAreaLaw := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, hC, hbound⟩ := harea q (by omega) J Δ hJ hΔ
  refine ⟨C, hC, fun L h E₀ Ω hΩ A ↦ ?_⟩
  exact (hbound L L h.toRectangularHamiltonian E₀ Ω hΩ A).1

end TNLean.PEPS.AreaLaw
