/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.FiniteDomain
import QICLean.ManyBody.Sites.Lattice.Rectangle
import TNLean.PEPS.Injectivity.Normal.NormalBlocking
import TNLean.PEPS.Tensor.Region.RegionBlock

/-!
# Native rectangular edge and vertex boundaries

Crossing edges are counted once using the native undirected edge type. The
inner boundary and all crossing-edge endpoints are QICLean's `ManyBody.innerBoundary` and
`ManyBody.endpointBoundary` of the native square-lattice graph. The integer-domain
identification preserves these sets and their cardinalities exactly, including zero side
lengths and empty boundaries.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Corollary 1.2 (`cor:rectangles`), at immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph)

noncomputable section

open TNLean.Lattice

open ManyBody (planeDomainGraph rectangularDomain rectangleSiteEquiv rectangleGraphIso)

open ManyBody (edgeBoundary innerBoundary endpointBoundary)

namespace TNLean.PEPS.AreaLaw

/-- The original crossing edges of a cut correspond bijectively to the crossing
edges of the transported cut in the integer rectangle. Source: polynomial-PEPS
`01-preliminaries.tex`, lines 47–50, definition of `∂_Λ A`, and area-law
Section 1. -/
theorem card_edgeBoundary_rectangular {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    (edgeBoundary (planeDomainGraph (rectangularDomain width height))
        (A.map (rectangleSiteEquiv width height).toEmbedding)).card =
      Fintype.card {e : Edge (squareLatticeGraph width height) // IsRegionBoundaryEdge A e} := by
  classical
  let σ := rectangleSiteEquiv width height
  have hadj : ∀ a b : SquareLatticeVertex width height,
      (planeDomainGraph (rectangularDomain width height)).Adj (σ a) (σ b) ↔
        (squareLatticeGraph width height).Adj a b :=
    fun a b ↦ (rectangleGraphIso width height).map_rel_iff
  have hmem : ∀ a : SquareLatticeVertex width height,
      σ a ∈ A.map σ.toEmbedding ↔ a ∈ A := fun a ↦ by simp [σ]
  rw [Fintype.card_subtype]
  symm
  refine Finset.card_bij (fun e _ ↦ s(σ e.1.1, σ e.1.2)) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he
    rw [ManyBody.mk_mem_edgeBoundary_iff, hadj, hmem, hmem]
    refine ⟨e.2.2, ?_⟩
    rcases he.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  · intro e _ f _ hef
    rcases Sym2.eq_iff.mp hef with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Subtype.ext (Prod.ext (σ.injective h₁) (σ.injective h₂))
    · have h₁ := σ.injective h₁
      have h₂ := σ.injective h₂
      have he := e.2.1
      have hf := f.2.1
      rw [h₁, h₂] at he
      exact (@lt_asymm (SquareLatticeVertex width height)
        instDistribLatticeOfLinearOrder.toSemilatticeInf.toPartialOrder.toPreorder _ _
        he hf).elim
  · intro z hz
    induction z using Sym2.ind with
    | h x y =>
      rw [ManyBody.mk_mem_edgeBoundary_iff] at hz
      obtain ⟨hxy, hcut⟩ := hz
      obtain ⟨a, rfl⟩ := σ.surjective x
      obtain ⟨b, rfl⟩ := σ.surjective y
      rw [hadj] at hxy
      rw [hmem, hmem] at hcut
      refine ⟨ManyBody.Edge.ofAdj hxy, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        unfold IsRegionBoundaryEdge ManyBody.Edge.ofAdj
        split_ifs <;> tauto
      · unfold ManyBody.Edge.ofAdj
        split_ifs
        · rfl
        · exact Sym2.eq_swap

/-- The exact native inner-boundary cardinality: the integer-domain identification carries the
native inner boundary onto the domain inner boundary. Source: Corollary 1.2. -/
theorem card_innerBoundary_rectangular {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    (innerBoundary (planeDomainGraph (rectangularDomain width height))
      (A.map (rectangleSiteEquiv width height).toEmbedding)).card =
        (innerBoundary (squareLatticeGraph width height) A).card := by
  have h := congrArg Finset.card (ManyBody.innerBoundary_map (rectangleGraphIso width height) A)
  rw [Finset.card_map] at h
  exact h

/-- The exact native endpoint-boundary cardinality: the integer-domain identification carries
the native endpoint boundary onto the domain endpoint boundary. Source: Corollary 1.2. -/
theorem card_endpointBoundary_rectangular {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    (endpointBoundary (planeDomainGraph (rectangularDomain width height))
      (A.map (rectangleSiteEquiv width height).toEmbedding)).card =
        (endpointBoundary (squareLatticeGraph width height) A).card := by
  have h :=
    congrArg Finset.card (ManyBody.endpointBoundary_map (rectangleGraphIso width height) A)
  rw [Finset.card_map] at h
  exact h

/-- Each native inner-boundary vertex accounts for at most four edges.
Source: Corollary 1.2. -/
theorem rectangleEdgeBoundary_card_le_four_mul_innerBoundary_card {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    Fintype.card {e : Edge (squareLatticeGraph width height) // IsRegionBoundaryEdge A e} ≤
      4 * (innerBoundary (squareLatticeGraph width height) A).card := by
  have h := ManyBody.card_edgeBoundary_le_mul_card_innerBoundary
    (A := A.map (rectangleSiteEquiv width height).toEmbedding)
    (ManyBody.planeDomainGraph_degree_le_four (rectangularDomain width height))
  rwa [card_edgeBoundary_rectangular, card_innerBoundary_rectangular] at h

/-- Counting both native endpoints gives the factor two.
Source: Corollary 1.2. -/
theorem rectangleEdgeBoundary_card_le_two_mul_endpointBoundary_card {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    Fintype.card {e : Edge (squareLatticeGraph width height) // IsRegionBoundaryEdge A e} ≤
      2 * (endpointBoundary (squareLatticeGraph width height) A).card := by
  have h := ManyBody.two_mul_card_edgeBoundary_le_mul_card_endpointBoundary
    (A := A.map (rectangleSiteEquiv width height).toEmbedding)
    (ManyBody.planeDomainGraph_degree_le_four (rectangularDomain width height))
  rw [card_edgeBoundary_rectangular, card_endpointBoundary_rectangular] at h
  omega

end TNLean.PEPS.AreaLaw
