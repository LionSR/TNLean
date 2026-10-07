/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteDomain
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Edge and vertex boundaries of a lattice cut

For a cut in an arbitrary finite induced square-lattice domain, the inner
boundary consists of the sites in the cut incident to a crossing edge. The
endpoint boundary consists of both endpoints of all crossing edges. Counting
degrees gives the factors four and two in the vertex-boundary formulations
of the area law. Empty and disconnected domains are allowed.

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
Provenance-ID: 8759-tnlean.peps.arealaw.innerboundary
Downstream declaration: TNLean.PEPS.AreaLaw.innerBoundary
Provenance-ID: 8759-tnlean.peps.arealaw.endpointboundary
Downstream declaration: TNLean.PEPS.AreaLaw.endpointBoundary
Provenance-ID: 8759-tnlean.peps.arealaw.innerboundary_empty
Downstream declaration: TNLean.PEPS.AreaLaw.innerBoundary_empty
Provenance-ID: 8759-tnlean.peps.arealaw.innerboundary_univ
Downstream declaration: TNLean.PEPS.AreaLaw.innerBoundary_univ
Provenance-ID: 8759-tnlean.peps.arealaw.endpointboundary_empty
Downstream declaration: TNLean.PEPS.AreaLaw.endpointBoundary_empty
Provenance-ID: 8759-tnlean.peps.arealaw.endpointboundary_univ
Downstream declaration: TNLean.PEPS.AreaLaw.endpointBoundary_univ
Provenance-ID: 8759-tnlean.peps.arealaw.domaingraph_degree_le_four
Downstream declaration: TNLean.PEPS.AreaLaw.domainGraph_degree_le_four
Provenance-ID: 8759-tnlean.peps.arealaw.edgeboundary_card_le_four_mul_innerboundary_card
Downstream declaration: TNLean.PEPS.AreaLaw.edgeBoundary_card_le_four_mul_innerBoundary_card
Provenance-ID: 8759-tnlean.peps.arealaw.edgeboundary_card_le_two_mul_endpointboundary_card
Downstream declaration: TNLean.PEPS.AreaLaw.edgeBoundary_card_le_two_mul_endpointBoundary_card
-/

namespace TNLean.PEPS.AreaLaw

/-- Sites of the cut adjacent to its complement.
Source: area-law Corollary 1.2, definition of the inner boundary. -/
noncomputable def innerBoundary (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    Finset (Site Λ) := by
  classical
  exact A.filter fun x ↦ ∃ y ∉ A, (domainGraph Λ).Adj x y

/-- Both endpoints of all crossing edges.
Source: area-law Corollary 1.2, definition of `Z_A`. -/
noncomputable def endpointBoundary (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    Finset (Site Λ) := by
  classical
  exact (edgeBoundary Λ A).biUnion Sym2.toFinset

/-- The empty cut has no inner-boundary sites.
Source: area-law Corollary 1.2, including empty boundaries. -/
@[simp] theorem innerBoundary_empty (Λ : Finset (ℤ × ℤ)) :
    innerBoundary Λ ∅ = ∅ := by
  classical
  simp [innerBoundary]

/-- The whole domain has no inner-boundary sites.
Source: area-law Corollary 1.2, including empty boundaries. -/
@[simp] theorem innerBoundary_univ (Λ : Finset (ℤ × ℤ)) :
    innerBoundary Λ Finset.univ = ∅ := by
  classical
  simp [innerBoundary]

/-- The empty cut has no boundary endpoints.
Source: area-law Corollary 1.2, including empty boundaries. -/
@[simp] theorem endpointBoundary_empty (Λ : Finset (ℤ × ℤ)) :
    endpointBoundary Λ ∅ = ∅ := by
  classical
  simp [endpointBoundary]

/-- The whole domain has no boundary endpoints.
Source: area-law Corollary 1.2, including empty boundaries. -/
@[simp] theorem endpointBoundary_univ (Λ : Finset (ℤ × ℤ)) :
    endpointBoundary Λ Finset.univ = ∅ := by
  classical
  simp only [endpointBoundary, edgeBoundary_univ, Finset.biUnion_empty]

/-- Every site has at most four neighbors in the induced lattice graph.
Source: area-law Corollary 1.2, degree counting in its proof. -/
theorem domainGraph_degree_le_four (Λ : Finset (ℤ × ℤ)) (x : Site Λ) :
    (domainGraph Λ).degree x ≤ 4 := by
  classical
  have hcard := Finset.card_image_of_injective
    ((domainGraph Λ).neighborFinset x) (Subtype.val_injective (p := (· ∈ Λ)))
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hcard]
  refine (Finset.card_le_card (t :=
    {(x.1.1 + 1, x.1.2), (x.1.1 - 1, x.1.2),
      (x.1.1, x.1.2 + 1), (x.1.1, x.1.2 - 1)}) ?_).trans Finset.card_le_four
  simp only [Finset.image_subset_iff]
  intro y hy
  have hy := ((domainGraph Λ).mem_neighborFinset x y).mp hy
  simp only [domainGraph] at hy
  grind [Prod.ext_iff]

private theorem crossingGraph_edgeFinset (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    ((domainGraph Λ).between (↑A) (↑A)ᶜ).edgeFinset = edgeBoundary Λ A := by
  classical
  ext e
  obtain ⟨x, y⟩ := e
  simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, SimpleGraph.between_adj, Set.mem_compl_iff,
    Finset.mem_coe, Sym2.eq_iff]
  refine ⟨fun ⟨hxy, h⟩ ↦ ⟨hxy, h.elim
    (fun ⟨hx, hy⟩ ↦ ⟨x, hx, y, hy, Or.inl ⟨rfl, rfl⟩⟩)
    (fun ⟨hx, hy⟩ ↦ ⟨y, hy, x, hx, Or.inr ⟨rfl, rfl⟩⟩)⟩, ?_⟩
  rintro ⟨hxy, x', hx, y', hy, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨hxy, Or.inl ⟨hx, hy⟩⟩
  · exact ⟨hxy, Or.inr ⟨hy, hx⟩⟩

private theorem crossingGraph_isBipartiteWith (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) :
    ((domainGraph Λ).between (↑A) (↑A)ᶜ).IsBipartiteWith
      (↑(innerBoundary Λ A)) (↑(innerBoundary Λ Aᶜ)) := by
  classical
  exact ⟨Set.disjoint_left.mpr (fun x hx hy ↦
    (Finset.mem_compl.mp (Finset.mem_filter.mp hy).1) (Finset.mem_filter.mp hx).1),
    fun {x y} ⟨hxy, h⟩ ↦ h.elim
      (fun ⟨hx, hy⟩ ↦ Or.inl ⟨
        Finset.mem_filter.mpr ⟨hx, ⟨y, hy, hxy⟩⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hy,
          ⟨x, fun hn ↦ (Finset.mem_compl.mp hn) hx, hxy.symm⟩⟩⟩)
      (fun ⟨hx, hy⟩ ↦ Or.inr ⟨
        Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hx,
          ⟨y, fun hn ↦ (Finset.mem_compl.mp hn) hy, hxy⟩⟩,
        Finset.mem_filter.mpr ⟨hy, ⟨x, hx, hxy.symm⟩⟩⟩)⟩

private theorem endpointBoundary_eq_support (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) :
    (endpointBoundary Λ A : Set (Site Λ)) =
      ((domainGraph Λ).between (↑A) (↑A)ᶜ).support := by
  classical
  ext x
  simp only [endpointBoundary, ← crossingGraph_edgeFinset, Finset.mem_coe,
    Finset.mem_biUnion, Sym2.mem_toFinset, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_support_iff_not_isIsolated,
    SimpleGraph.not_isIsolated_iff_exists_edgeSet_mem]

/-- Each inner-boundary site is incident to at most four crossing edges.
Source: area-law Corollary 1.2, first upper bound in its proof. -/
theorem edgeBoundary_card_le_four_mul_innerBoundary_card
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    (edgeBoundary Λ A).card ≤ 4 * (innerBoundary Λ A).card := by
  classical
  let G := (domainGraph Λ).between (↑A) (↑A)ᶜ
  let : DecidableRel G.Adj := inferInstanceAs
    (DecidableRel ((domainGraph Λ).between (↑A) (↑A)ᶜ).Adj)
  have hsum : ∑ x ∈ innerBoundary Λ A, G.degree x = (edgeBoundary Λ A).card :=
    (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
      (crossingGraph_isBipartiteWith Λ A)).trans (congrArg Finset.card
        (crossingGraph_edgeFinset Λ A))
  rw [← hsum]
  calc
    _ ≤ ∑ x ∈ innerBoundary Λ A, 4 := Finset.sum_le_sum fun x _ ↦
      (G.degree_le_of_le (H := domainGraph Λ) SimpleGraph.between_le).trans
        (domainGraph_degree_le_four Λ x)
    _ = 4 * (innerBoundary Λ A).card := by simp [Nat.mul_comm]

/-- Counting both endpoints of every crossing edge gives a factor two.
Source: area-law Corollary 1.2, second upper bound in its proof. -/
theorem edgeBoundary_card_le_two_mul_endpointBoundary_card
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    (edgeBoundary Λ A).card ≤ 2 * (endpointBoundary Λ A).card := by
  classical
  let G := (domainGraph Λ).between (↑A) (↑A)ᶜ
  let : DecidableRel G.Adj := inferInstanceAs
    (DecidableRel ((domainGraph Λ).between (↑A) (↑A)ᶜ).Adj)
  have hs : G.support.toFinset = endpointBoundary Λ A :=
    Finset.coe_injective ((Set.coe_toFinset _).trans (endpointBoundary_eq_support Λ A).symm)
  have hsum := G.sum_degrees_support_eq_twice_card_edges
  rw [hs, crossingGraph_edgeFinset] at hsum
  have hbound : ∑ x ∈ endpointBoundary Λ A, G.degree x ≤
      4 * (endpointBoundary Λ A).card := by
    calc
      _ ≤ ∑ x ∈ endpointBoundary Λ A, 4 := Finset.sum_le_sum fun x _ ↦
        (G.degree_le_of_le (H := domainGraph Λ) SimpleGraph.between_le).trans
          (domainGraph_degree_le_four Λ x)
      _ = 4 * (endpointBoundary Λ A).card := by simp [Nat.mul_comm]
  omega

end TNLean.PEPS.AreaLaw
