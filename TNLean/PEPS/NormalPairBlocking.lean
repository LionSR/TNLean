import TNLean.PEPS.NormalBlocking
import TNLean.PEPS.RegionBlock.UnionClosure
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Shared blocking data for two normal PEPS tensors

The general normal PEPS theorem (arXiv:1804.04964, Section 3, theorem labelled
`normal`, lines 1576--1583 of `Papers/1804.04964/paper_normal.tex`) assumes
that *two* normal PEPS generating the same state "can be blocked into three
partite injective MPS around every edge" and that "for every site, there are
injective regions with their complements also being injective that differ only
in the given site".  The blockings are shared between the two states: the
source's final comparison contracts both tensors over the *same* regions, so
each region in the hypothesis must be injective for both tensors at once.

This file records that pairing at the level of the abstract region-injectivity
predicate: the conjunction predicate `regionInjectivityDataPair` declares a
region injective when it is injective for each of the two tensors, and a
one-edge blocking datum over the conjunction projects to a datum over either
single-tensor predicate with the same three regions.  It also proves the two
small geometric facts the assembly needs: a region that is neither empty nor
the full vertex set has a boundary edge on a connected graph, and the
one-site-different region pair is an `insert`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, theorem labelled `normal`, lines 1576--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The conjunction of two region-injectivity predicates -/

/-- The conjunction of two region-injectivity predicates: a region is injective
when it is injective for each of the two tensors.

The general normal PEPS theorem blocks *two* states by one shared geometry, and
the source's final comparison applies the inverses of both blocked tensors over
the same regions, so the blocking hypothesis asks each region to be injective
for both tensors at once.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
def regionInjectivityDataPair (κ κ' : RegionInjectivityData V) :
    RegionInjectivityData V where
  IsInjective R := κ.IsInjective R ∧ κ'.IsInjective R

omit [Fintype V] [LinearOrder V] in
@[simp] theorem regionInjectivityDataPair_isInjective
    (κ κ' : RegionInjectivityData V) (R : Finset V) :
    (regionInjectivityDataPair κ κ').IsInjective R ↔
      κ.IsInjective R ∧ κ'.IsInjective R :=
  Iff.rfl

/-! ### Projections of a one-edge blocking datum

A one-edge blocking datum over a stronger predicate projects to a datum over a
weaker one with the same three regions; in particular a datum over the
conjunction predicate projects to a datum over either single-tensor predicate. -/

/-- Weaken the region-injectivity predicate of a one-edge blocking datum: any
predicate implied by the original one accepts the same three regions.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex` (the blocking regions are shared; only the
injectivity assertion is projected). -/
def NormalEdgeBlockingData.ofLE {ι κ : RegionInjectivityData V} {e : Edge G}
    (D : NormalEdgeBlockingData ι G e)
    (h : ∀ R : Finset V, ι.IsInjective R → κ.IsInjective R) :
    NormalEdgeBlockingData κ G e where
  red := D.red
  blue := D.blue
  complement := D.complement
  left_mem_red := D.left_mem_red
  right_mem_blue := D.right_mem_blue
  red_injective := h _ D.red_injective
  blue_injective := h _ D.blue_injective
  complement_injective := h _ D.complement_injective
  red_disjoint_blue := D.red_disjoint_blue
  red_disjoint_complement := D.red_disjoint_complement
  blue_disjoint_complement := D.blue_disjoint_complement
  cover_univ := D.cover_univ

/-- The first projection of a one-edge blocking datum over the conjunction
predicate: the same three regions, injective for the first tensor.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
def NormalEdgeBlockingData.pairLeft {κ κ' : RegionInjectivityData V} {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataPair κ κ') G e) :
    NormalEdgeBlockingData κ G e :=
  D.ofLE fun _ h => h.1

/-- The second projection of a one-edge blocking datum over the conjunction
predicate: the same three regions, injective for the second tensor.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
def NormalEdgeBlockingData.pairRight {κ κ' : RegionInjectivityData V} {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataPair κ κ') G e) :
    NormalEdgeBlockingData κ' G e :=
  D.ofLE fun _ h => h.2

omit [DecidableRel G.Adj] in
@[simp] theorem NormalEdgeBlockingData.pairLeft_red
    {κ κ' : RegionInjectivityData V} {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataPair κ κ') G e) :
    D.pairLeft.red = D.red := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem NormalEdgeBlockingData.pairLeft_blue
    {κ κ' : RegionInjectivityData V} {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataPair κ κ') G e) :
    D.pairLeft.blue = D.blue := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem NormalEdgeBlockingData.pairLeft_complement
    {κ κ' : RegionInjectivityData V} {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataPair κ κ') G e) :
    D.pairLeft.complement = D.complement := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem NormalEdgeBlockingData.pairRight_red
    {κ κ' : RegionInjectivityData V} {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataPair κ κ') G e) :
    D.pairRight.red = D.red := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem NormalEdgeBlockingData.pairRight_blue
    {κ κ' : RegionInjectivityData V} {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataPair κ κ') G e) :
    D.pairRight.blue = D.blue := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem NormalEdgeBlockingData.pairRight_complement
    {κ κ' : RegionInjectivityData V} {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataPair κ κ') G e) :
    D.pairRight.complement = D.complement := rfl

/-! ### Boundary edges of a proper region on a connected graph

A region that is neither empty nor the full vertex set has a boundary edge on a
connected graph: a walk from a vertex inside the region to a vertex outside it
crosses the boundary at some step. -/

omit [DecidableRel G.Adj] in
/-- On a connected graph, a nonempty region different from the full vertex set
has a boundary edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex` (the comparison regions are compared
through their boundary bonds, which exist because the lattice is connected). -/
theorem nonempty_regionBoundaryEdge_of_connected (hconn : G.Connected)
    {R : Finset V} (hR : R.Nonempty) (hRtop : R ≠ Finset.univ) :
    Nonempty {f : Edge G // IsRegionBoundaryEdge (G := G) R f} := by
  classical
  obtain ⟨u, hu⟩ := hR
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ R := by
    by_contra hall
    push Not at hall
    exact hRtop (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨p⟩ := hconn.preconnected u w
  obtain ⟨dart, -, hd1, hd2⟩ :=
    p.exists_boundary_dart (↑R : Set V) (by simpa using hu) (by simpa using hw)
  have hd1' : dart.fst ∈ R := by simpa using hd1
  have hd2' : dart.snd ∉ R := by simpa using hd2
  rcases Edge.ofAdj_endpoints dart.adj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨Edge.ofAdj dart.adj, Or.inl ⟨h1.symm ▸ hd1', h2.symm ▸ hd2'⟩⟩⟩
  · exact ⟨⟨Edge.ofAdj dart.adj, Or.inr ⟨h1.symm ▸ hd2', h2.symm ▸ hd1'⟩⟩⟩

/-! ### The one-site comparison pair as an `insert` -/

/-- The region containing the distinguished site is the comparison region with
that site inserted.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex` (the two regions differ only
in the given site). -/
theorem NormalOneSiteSeparationHypotheses.withSite_eq_insert
    {ι : RegionInjectivityData V} (h : NormalOneSiteSeparationHypotheses ι)
    (v : V) :
    h.withSite v = insert v (h.withoutSite v) := by
  ext w
  rw [h.mem_withSite_iff v w, Finset.mem_insert]

end PEPS
end TNLean
