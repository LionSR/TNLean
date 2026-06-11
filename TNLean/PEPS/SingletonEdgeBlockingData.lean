import TNLean.PEPS.NormalEdgeBlockingData
import TNLean.PEPS.RegionBlock.UnionClosure
import TNLean.PEPS.RegionBlock.CoarseThreeSite2
import TNLean.PEPS.IsoTransport

/-!
# Singleton-endpoint blocking data for a vertex-injective PEPS

For a vertex-injective PEPS with positive bond dimensions, every finite vertex region is
blocked-tensor injective (a contraction of injective tensors is injective,
`regionBlockedTensorInjective_of_isVertexInjective`).  This removes the rectangular-cover
bookkeeping of the open-lattice every-edge construction: at any edge `e` the singleton red block
`{e.1.1}`, the singleton blue block `{e.1.2}`, and the complementary block `univ \ {e.1.1, e.1.2}`
partition the vertex set, all three are injective, and the only red-to-blue crossing is `e` itself.

The construction is graph-polymorphic, so it applies verbatim to the discrete torus at any
reference edge: it produces the reference blocking datum the translation-invariant gauge family
consumes, with the single-crossing hypothesis discharged unconditionally.  The wraparound geometry
of the torus never enters, because singleton blocks need no room to be injective once the tensor is
vertex injective.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 981--1009 and
  1322--1404 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Singleton red-to-blue crossing

For two distinct singleton blocks `{p}` and `{q}`, an edge crosses between them precisely when its
two endpoints are `p` and `q` in some order, i.e. the edge is `Edge.ofAdj` on the adjacent pair.
This is the singleton form of the single-crossing hypothesis. -/

omit [Fintype V] [DecidableEq V] in
/-- An edge crosses between the singleton blocks `{p}` and `{q}` exactly when its unordered
endpoint pair is `{p, q}`. -/
theorem isCrossingEdge_singleton (A : Tensor G d) {p q : V} (hpq : p ≠ q)
    (g : Edge G) :
    IsCrossingEdge (G := G) A ({p} : Finset V) ({q} : Finset V) g ↔
      (g.1.1 = p ∧ g.1.2 = q) ∨ (g.1.1 = q ∧ g.1.2 = p) := by
  classical
  unfold IsCrossingEdge IsRegionBoundaryEdge
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hP, hQ⟩
    -- From the `{p}` boundary, exactly one endpoint is `p`; from `{q}`, exactly one is `q`.
    rcases hP with ⟨h1p, h2p⟩ | ⟨h1p, h2p⟩
    · -- `g.1.1 = p`, `g.1.2 ≠ p`.  Then the `{q}` boundary forces `g.1.2 = q`.
      rcases hQ with ⟨h1q, _⟩ | ⟨_, h2q⟩
      · exact absurd (h1q.symm.trans h1p) hpq.symm
      · exact Or.inl ⟨h1p, h2q⟩
    · -- `g.1.1 ≠ p`, `g.1.2 = p`.  Then the `{q}` boundary forces `g.1.1 = q`.
      rcases hQ with ⟨h1q, _⟩ | ⟨_, h2q⟩
      · exact Or.inr ⟨h1q, h2p⟩
      · exact absurd (h2q.symm.trans h2p) hpq.symm
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · -- `g.1.1 = p`, `g.1.2 = q`.
      refine ⟨Or.inl ⟨h1, ?_⟩, Or.inr ⟨?_, h2⟩⟩
      · rw [h2]; exact fun h => hpq h.symm
      · rw [h1]; exact hpq
    · -- `g.1.1 = q`, `g.1.2 = p`.
      refine ⟨Or.inr ⟨?_, h2⟩, Or.inl ⟨h1, ?_⟩⟩
      · rw [h1]; exact fun h => hpq h.symm
      · rw [h2]; exact hpq

omit [Fintype V] [DecidableEq V] in
/-- The single red-to-blue crossing between `{p}` and `{q}` for adjacent distinct `p`, `q` is the
edge `Edge.ofAdj` on the pair: an edge crosses between the two singletons iff it is that edge. -/
theorem isCrossingEdge_singleton_eq_ofAdj (A : Tensor G d) {p q : V} (hadj : G.Adj p q)
    (g : Edge G) :
    IsCrossingEdge (G := G) A ({p} : Finset V) ({q} : Finset V) g ↔ g = Edge.ofAdj hadj := by
  rw [isCrossingEdge_singleton A (G.ne_of_adj hadj) g]
  constructor
  · intro h
    refine (Edge.ofAdj_eq_of_endpoints hadj g ?_).symm
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  · intro h
    subst h
    exact Edge.ofAdj_endpoints hadj

/-! ### The singleton blocking datum -/

/-- **Singleton-endpoint blocking datum.**

For a vertex-injective PEPS `A` with positive bond dimensions, the edge `e` has a one-edge blocking
datum whose red block is the singleton `{e.1.1}`, blue block the singleton `{e.1.2}`, and
complementary block `univ \ {e.1.1, e.1.2}`.  All three regions are injective because every finite
region is injective under vertex injectivity; the three regions partition the vertex set; the edge's
left endpoint lies in red and right endpoint in blue.

This is the cover-free reference blocking datum: it needs no rectangular geometry, so it applies on
any graph, including the discrete torus at a reference edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 981--1009 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def singletonEdgeBlockingData (A : Tensor G d) (e : Edge G)
    (hA : IsVertexInjective A) (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e where
  red := {e.1.1}
  blue := {e.1.2}
  complement := Finset.univ \ ({e.1.1} ∪ {e.1.2})
  left_mem_red := Finset.mem_singleton_self e.1.1
  right_mem_blue := Finset.mem_singleton_self e.1.2
  red_injective := by
    rw [regionInjectivityDataOf_isInjective]
    exact regionBlockedTensorInjective_of_isVertexInjective (G := G) A {e.1.1} hA hpos
  blue_injective := by
    rw [regionInjectivityDataOf_isInjective]
    exact regionBlockedTensorInjective_of_isVertexInjective (G := G) A {e.1.2} hA hpos
  complement_injective := by
    rw [regionInjectivityDataOf_isInjective]
    exact regionBlockedTensorInjective_of_isVertexInjective (G := G) A
      (Finset.univ \ ({e.1.1} ∪ {e.1.2})) hA hpos
  red_disjoint_blue := by
    rw [Finset.disjoint_singleton]
    exact (G.ne_of_adj e.2.2)
  red_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    rw [Finset.mem_sdiff] at hxc
    exact hxc.2 (Finset.mem_union_left _ hx)
  blue_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    rw [Finset.mem_sdiff] at hxc
    exact hxc.2 (Finset.mem_union_right _ hx)
  cover_univ := by
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]

@[simp] theorem singletonEdgeBlockingData_red (A : Tensor G d) (e : Edge G)
    (hA : IsVertexInjective A) (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    (singletonEdgeBlockingData A e hA hpos).red = ({e.1.1} : Finset V) := rfl

@[simp] theorem singletonEdgeBlockingData_blue (A : Tensor G d) (e : Edge G)
    (hA : IsVertexInjective A) (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    (singletonEdgeBlockingData A e hA hpos).blue = ({e.1.2} : Finset V) := rfl

@[simp] theorem singletonEdgeBlockingData_complement (A : Tensor G d) (e : Edge G)
    (hA : IsVertexInjective A) (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    (singletonEdgeBlockingData A e hA hpos).complement =
      Finset.univ \ ({e.1.1} ∪ {e.1.2}) := rfl

/-- The red-to-blue crossings of the singleton blocking datum are exactly the edge `e`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_singletonEdgeBlockingData (A : Tensor G d) (e : Edge G)
    (hA : IsVertexInjective A) (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (g : Edge G) :
    IsCrossingEdge (G := G) A (singletonEdgeBlockingData A e hA hpos).red
        (singletonEdgeBlockingData A e hA hpos).blue g ↔
      g = e := by
  rw [singletonEdgeBlockingData_red, singletonEdgeBlockingData_blue,
    isCrossingEdge_singleton_eq_ofAdj A e.2.2 g, Edge.ofAdj_fst_snd]

end PEPS
end TNLean
