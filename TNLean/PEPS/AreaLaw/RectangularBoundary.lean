/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularDomain
import TNLean.PEPS.AreaLaw.EdgeBoundaryCalculus
import TNLean.PEPS.AreaLaw.BoundaryConventions
import TNLean.PEPS.RegionBlock.Basic

/-!
# Native rectangular edge and vertex boundaries

Crossing edges are counted once using the native undirected edge type. The
inner boundary and all crossing-edge endpoints are defined in native vertex
coordinates. The integer-domain identification preserves these sets and their
cardinalities exactly, including zero side lengths and empty boundaries.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Corollary 1.2 (`cor:rectangles`), at immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw

/-- Native sites in a cut adjacent to its complement. Source: Corollary 1.2. -/
def rectangleInnerBoundary {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    Finset (SquareLatticeVertex width height) :=
  A.filter fun x ↦ ∃ y ∉ A, (squareLatticeGraph width height).Adj x y

/-- Both native endpoints of the crossing edges. Source: Corollary 1.2,
`Z_A`; the adjacency and opposite-side conditions make this the endpoint union. -/
def rectangleEndpointBoundary {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    Finset (SquareLatticeVertex width height) :=
  Finset.univ.filter fun x ↦ ∃ y, (squareLatticeGraph width height).Adj x y ∧
    ((x ∈ A ∧ y ∉ A) ∨ (y ∈ A ∧ x ∉ A))

/-- The original crossing edges of a cut correspond bijectively to the crossing
edges of the transported cut in the integer rectangle. Source: polynomial-PEPS
`01-preliminaries.tex`, lines 47–50, definition of `∂_Λ A`, and area-law
Section 1. -/
theorem card_edgeBoundary_rectangular {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    (edgeBoundary (rectangularDomain width height)
        (A.map (rectangleSiteEquiv width height).toEmbedding)).card =
      Fintype.card {e : Edge (squareLatticeGraph width height) // IsRegionBoundaryEdge A e} := by
  classical
  let σ := rectangleSiteEquiv width height
  have hadj : ∀ a b : SquareLatticeVertex width height,
      (domainGraph (rectangularDomain width height)).Adj (σ a) (σ b) ↔
        (squareLatticeGraph width height).Adj a b :=
    fun a b ↦ (rectangleGraphIso width height).map_rel_iff
  have hmem : ∀ a : SquareLatticeVertex width height,
      σ a ∈ A.map σ.toEmbedding ↔ a ∈ A := fun a ↦ by simp [σ]
  rw [Fintype.card_subtype]
  symm
  refine Finset.card_bij (fun e _ ↦ s(σ e.1.1, σ e.1.2)) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he
    rw [mem_edgeBoundary_pair_iff, hadj, hmem, hmem]
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
      rw [mem_edgeBoundary_pair_iff] at hz
      obtain ⟨hxy, hcut⟩ := hz
      obtain ⟨a, rfl⟩ := σ.surjective x
      obtain ⟨b, rfl⟩ := σ.surjective y
      rw [hadj] at hxy
      rw [hmem, hmem] at hcut
      refine ⟨Edge.ofAdj hxy, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        unfold IsRegionBoundaryEdge Edge.ofAdj
        split_ifs <;> tauto
      · unfold Edge.ofAdj
        split_ifs
        · rfl
        · exact Sym2.eq_swap

/-- Membership in the domain endpoint union is adjacency across the cut.
Source: Corollary 1.2, definition of `Z_A`. -/
theorem mem_endpointBoundary_iff_adj {Λ : Finset (ℤ × ℤ)}
    (A : Finset (Site Λ)) (x : Site Λ) :
    x ∈ endpointBoundary Λ A ↔ ∃ y, (domainGraph Λ).Adj x y ∧
      ((x ∈ A ∧ y ∉ A) ∨ (y ∈ A ∧ x ∉ A)) := by
  classical
  simp only [endpointBoundary, Finset.mem_biUnion, Sym2.mem_toFinset,
    Sym2.mem_iff_exists]
  constructor
  · rintro ⟨e, he, y, rfl⟩
    exact ⟨y, (mem_edgeBoundary_pair_iff A x y).mp he⟩
  · rintro ⟨y, hy⟩
    exact ⟨s(x, y), (mem_edgeBoundary_pair_iff A x y).mpr hy, y, rfl⟩

/-- The native inner boundary maps to exactly the integer-domain inner boundary.
Source: Corollary 1.2. -/
theorem map_rectangleInnerBoundary {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    (rectangleInnerBoundary A).map (rectangleSiteEquiv width height).toEmbedding =
      innerBoundary (rectangularDomain width height)
        (A.map (rectangleSiteEquiv width height).toEmbedding) := by
  classical
  let σ := rectangleSiteEquiv width height
  have hadj (a b : SquareLatticeVertex width height) :
      (domainGraph (rectangularDomain width height)).Adj (σ a) (σ b) ↔
        (squareLatticeGraph width height).Adj a b :=
    (rectangleGraphIso width height).map_rel_iff
  have hmem (a : SquareLatticeVertex width height) :
      σ a ∈ A.map (rectangleSiteEquiv width height).toEmbedding ↔ a ∈ A := by
    simp [σ]
  ext x
  obtain ⟨a, rfl⟩ := σ.surjective x
  have hm : σ a ∈ (rectangleInnerBoundary A).map σ.toEmbedding ↔
      a ∈ rectangleInnerBoundary A := by simp
  rw [hm]
  simp only [rectangleInnerBoundary, innerBoundary, Finset.mem_filter, hmem]
  constructor
  · rintro ⟨ha, b, hb, hab⟩
    exact ⟨ha, σ b, fun h ↦ hb ((hmem b).mp h), (hadj a b).mpr hab⟩
  · rintro ⟨ha, y, hy, hay⟩
    obtain ⟨b, rfl⟩ := σ.surjective y
    exact ⟨ha, b, fun h ↦ hy ((hmem b).mpr h), (hadj a b).mp hay⟩

/-- The native endpoint union maps to exactly the domain endpoint union.
Source: Corollary 1.2. -/
theorem map_rectangleEndpointBoundary {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    (rectangleEndpointBoundary A).map (rectangleSiteEquiv width height).toEmbedding =
      endpointBoundary (rectangularDomain width height)
        (A.map (rectangleSiteEquiv width height).toEmbedding) := by
  classical
  let σ := rectangleSiteEquiv width height
  have hadj (a b : SquareLatticeVertex width height) :
      (domainGraph (rectangularDomain width height)).Adj (σ a) (σ b) ↔
        (squareLatticeGraph width height).Adj a b :=
    (rectangleGraphIso width height).map_rel_iff
  have hmem (a : SquareLatticeVertex width height) :
      σ a ∈ A.map (rectangleSiteEquiv width height).toEmbedding ↔ a ∈ A := by
    simp [σ]
  ext x
  obtain ⟨a, rfl⟩ := σ.surjective x
  have hm : σ a ∈ (rectangleEndpointBoundary A).map σ.toEmbedding ↔
      a ∈ rectangleEndpointBoundary A := by simp
  rw [hm, mem_endpointBoundary_iff_adj]
  simp only [rectangleEndpointBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, hab, hcut⟩
    refine ⟨σ b, (hadj a b).mpr hab, ?_⟩
    simpa only [hmem] using hcut
  · rintro ⟨y, hay, hcut⟩
    obtain ⟨b, rfl⟩ := σ.surjective y
    refine ⟨b, (hadj a b).mp hay, ?_⟩
    simpa only [hmem] using hcut

/-- The exact native inner-boundary cardinality. Source: Corollary 1.2. -/
theorem card_innerBoundary_rectangular {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    (innerBoundary (rectangularDomain width height)
      (A.map (rectangleSiteEquiv width height).toEmbedding)).card =
        (rectangleInnerBoundary A).card := by
  rw [← map_rectangleInnerBoundary, Finset.card_map]

/-- The exact native endpoint-boundary cardinality. Source: Corollary 1.2. -/
theorem card_endpointBoundary_rectangular {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    (endpointBoundary (rectangularDomain width height)
      (A.map (rectangleSiteEquiv width height).toEmbedding)).card =
        (rectangleEndpointBoundary A).card := by
  rw [← map_rectangleEndpointBoundary, Finset.card_map]

/-- Each native inner-boundary vertex accounts for at most four edges.
Source: Corollary 1.2. -/
theorem rectangleEdgeBoundary_card_le_four_mul_innerBoundary_card {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    Fintype.card {e : Edge (squareLatticeGraph width height) // IsRegionBoundaryEdge A e} ≤
      4 * (rectangleInnerBoundary A).card := by
  have h := edgeBoundary_card_le_four_mul_innerBoundary_card
    (rectangularDomain width height) (A.map (rectangleSiteEquiv width height).toEmbedding)
  rwa [card_edgeBoundary_rectangular, card_innerBoundary_rectangular] at h

/-- Counting both native endpoints gives the factor two.
Source: Corollary 1.2. -/
theorem rectangleEdgeBoundary_card_le_two_mul_endpointBoundary_card {width height : ℕ}
    (A : Finset (SquareLatticeVertex width height)) :
    Fintype.card {e : Edge (squareLatticeGraph width height) // IsRegionBoundaryEdge A e} ≤
      2 * (rectangleEndpointBoundary A).card := by
  have h := edgeBoundary_card_le_two_mul_endpointBoundary_card
    (rectangularDomain width height) (A.map (rectangleSiteEquiv width height).toEmbedding)
  rwa [card_edgeBoundary_rectangular, card_endpointBoundary_rectangular] at h

end TNLean.PEPS.AreaLaw
