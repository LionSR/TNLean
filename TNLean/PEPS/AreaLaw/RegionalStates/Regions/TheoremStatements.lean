/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.SupportCounting
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Sites.Config
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Sites.Lattice.Plane
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Entropy.PlaneBoundaryEntropy
import QICLean.Analysis.Support.ProjectionOrder
import QICLean.ManyBody.Hamiltonian.FrustrationFree

/-!
# Statements of the two-dimensional area laws

The uniform finite-domain area law of Theorem 1.1 as the predicate `UniformAreaLaw`, its
vertex-boundary forms, and the goal of the frustration-free area-law note.

* `TNLean.PEPS.AreaLaw.UniformAreaLaw`: the uniform finite-domain area-law statement.
* `TNLean.PEPS.AreaLaw.UniformAreaLaw.vertex_boundary_bounds`: an edge-boundary area law with
  a nonnegative constant implies the inner-boundary and endpoint-boundary formulations, with
  factors four and two, keeping the constant independent of the domain, the interaction
  family, the ground vector and the cut. The edge-boundary area law is a hypothesis.
* `TNLean.PEPS.AreaLaw.FrustrationFree.FrustrationFreeAreaLaw`: the goal `eq:goal` of the
  frustration-free note, for the model `ManyBody.IsFrustrationFreeGapped` (`eq:model`).
* `TNLean.PEPS.AreaLaw.UniformAreaLaw.frustrationFreeAreaLaw`: the general area law implies
  that goal.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 (`00-introduction.tex`, lines 39–53) and Corollary 1.2
  (`cor:rectangles`, lines 59–85), at source revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  "Setting", `eq:model` and `eq:goal`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (regionEntropy_le_four_mul_innerBoundary_card
  regionEntropy_le_two_mul_endpointBoundary_card)

open scoped Matrix.Norms.L2Operator
open ManyBody (IsGapped groundSpace PlaneInteraction)

section TheoremStatements

/-!
## The uniform finite-domain area-law statement

The constant is chosen before the finite domain, interaction family, ground
vector, and cut. Regional entropy is the von Neumann entropy of the partial
trace, `ManyBody.regionEntropy`. The target is a proposition; this
module does not assert that the area law has been proved.

### Main definitions

* `UniformAreaLaw`: the complete arbitrary-domain, finite-range target.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 and `eq:area-law`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (planeDomainGraph edgeBoundary)

namespace TNLean.PEPS.AreaLaw

/-- The uniform area-law target, with its constant chosen before all physical
instances. Source: area-law Theorem 1.1 (`thm:area`, `eq:area-law`).
This proposition is a theorem statement, not a proof of that theorem. -/
def UniformAreaLaw : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : PlaneInteraction Λ q R, (∀ X, (h.term X).IsHermitian) →
          (∀ X, ‖h.term X‖ ≤ J) →
        ∀ E₀ : ℝ, ∀ Ω : EuclideanSpace ℂ (↥Λ → Fin q),
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
            ∀ A : Finset ↥Λ,
              ManyBody.regionEntropy Ω A ≤ C * (edgeBoundary (planeDomainGraph Λ) A).card

end TNLean.PEPS.AreaLaw

end TheoremStatements

section VertexBoundaryCorollaries

open ManyBody (planeDomainGraph edgeBoundary innerBoundary endpointBoundary)

namespace TNLean.PEPS.AreaLaw

/-- A uniform edge-boundary area law implies both uniform vertex-boundary bounds.
Source: area-law Corollary 1.2. The area-law theorem is an explicit hypothesis,
and the same constant is chosen before all physical instances and cuts. -/
theorem UniformAreaLaw.vertex_boundary_bounds (h : UniformAreaLaw) :
    ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Λ : Finset (ℤ × ℤ), ∀ H : PlaneInteraction Λ q R, (∀ X, (H.term X).IsHermitian) →
            (∀ X, ‖H.term X‖ ≤ J) →
          ∀ E₀ : ℝ, ∀ Ω : EuclideanSpace ℂ (↥Λ → Fin q),
            ‖Ω‖ = 1 → IsGapped H.hamiltonian E₀ Δ →
            groundSpace H.hamiltonian E₀ = Submodule.span ℂ {Ω} →
              ∀ A : Finset ↥Λ,
                ManyBody.regionEntropy Ω A ≤
                    4 * C * (innerBoundary (planeDomainGraph Λ) A).card ∧
                ManyBody.regionEntropy Ω A ≤
                    2 * C * (endpointBoundary (planeDomainGraph Λ) A).card := by
  intro q hq R J Δ hJ hΔ
  obtain ⟨C, hC, harea⟩ := h q hq R J Δ hJ hΔ
  exact ⟨C, hC, fun Λ H hH hHJ E₀ Ω hΩ hgap hspan A ↦
    ⟨regionEntropy_le_four_mul_innerBoundary_card hC (harea Λ H hH hHJ E₀ Ω hΩ hgap hspan A),
      regionEntropy_le_two_mul_endpointBoundary_card hC (harea Λ H hH hHJ E₀ Ω hΩ hgap hspan A)⟩⟩

end TNLean.PEPS.AreaLaw

end VertexBoundaryCorollaries

section FrustrationFreeAreaLaw

open ManyBody (IsFrustrationFreeGapped)

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open ManyBody (IsGapped groundSpace PlaneInteraction)
open ManyBody (planeDomainGraph edgeBoundary)

namespace TNLean.PEPS.AreaLaw.FrustrationFree

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ}

/-- **The frustration-free area law** (`eq:goal` of the frustration-free area-law note): for
`q ≥ 1`, `R`, and `J, Δ > 0` there is a constant `C`, chosen before the domain, the Hamiltonian
and the cut, with `S_Ω(A) ≤ C |∂_Λ A|` for every instance of `eq:model`. -/
def FrustrationFreeAreaLaw : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : PlaneInteraction Λ q R, ∀ Ω : EuclideanSpace ℂ (↥Λ → Fin q),
        IsFrustrationFreeGapped h J Δ Ω →
          ∀ A : Finset ↥Λ,
            ManyBody.regionEntropy Ω A ≤ C * (edgeBoundary (planeDomainGraph Λ) A).card

/-- **The general area law implies the frustration-free area law.** Every instance of
`eq:model` is gapped at energy zero with unique ground vector `Ω`, Hermitian terms and
`‖h_X‖ ≤ J`, so Theorem 1.1 applies. This proof passes through the filtered constraints of the
general theorem; the short route of the note is assembled separately. -/
theorem _root_.TNLean.PEPS.AreaLaw.UniformAreaLaw.frustrationFreeAreaLaw
    (hU : UniformAreaLaw) : FrustrationFreeAreaLaw := by
  intro q hq R J Δ hJ hΔ
  obtain ⟨C, hC, hbound⟩ := hU q hq R J Δ hJ hΔ
  exact ⟨C, hC, fun Λ h Ω hff A ↦ hbound Λ h (fun X ↦ (hff.posSemidef X).isHermitian)
    (hff.norm_term_le hJ.le) 0 Ω
    hff.norm_eq_one hff.isGapped hff.groundSpace_eq A⟩

end TNLean.PEPS.AreaLaw.FrustrationFree

end FrustrationFreeAreaLaw
