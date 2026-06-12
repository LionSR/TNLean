import TNLean.PEPS.CycleArcRegion
import TNLean.PEPS.NormalBlocking
import TNLean.PEPS.RegionBlock.CoarseThreeSite2

/-!
# Blocking data for normal MPS on the cycle graph

The first corollary after the general normal PEPS theorem (arXiv:1804.04964,
Section 3, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`) concerns
two MPS on a closed chain of `n ≥ 3L` sites such that blocking any `L`
consecutive sites gives an injective tensor.  This file builds, from that
arc-injectivity hypothesis, the blocking hypotheses consumed by the general
normal PEPS theorem on the cycle graph:

* around the edge joining a vertex to its cyclic successor, the chain is
  blocked into the `L` sites ending at the first endpoint, the `L` sites
  starting at the second, and the remaining `n - 2L ≥ L` sites — three
  injective blocks covering the chain;
* at every site, the `L + 1` sites starting at the site and the `L` sites
  starting at its successor are injective regions with injective complements
  differing exactly at the site;
* the only nearest-neighbour pair joining the two blocks around an edge is
  the edge itself, the single-crossing hypothesis of the general theorem.

Longer blocks of consecutive sites are injective as unions of length-`L`
blocks, which is the source's use of its union lemma (arXiv:1804.04964,
Section 3, Lemma labelled `injective_union`, lines 1322--1404).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, first corollary after the theorem labelled `normal`, lines
  1585--1622 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {n : ℕ}

/-! ### The arc-injectivity hypotheses -/

/-- The arc-injectivity hypotheses of the source corollary: every block of `L`
consecutive sites of the cycle is injective.  This is the cycle counterpart of
the torus `NormalTorusRectangleInjectivityHypotheses`.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`:
"blocking any `L` consecutive sites results in an injective tensor". -/
structure NormalCycleArcInjectivityHypotheses (L : ℕ) (κ : RegionInjectivityData (Fin n)) where
  /-- Every block of `L` consecutive sites is injective. -/
  arc_injective : ∀ s : Fin n, κ.IsInjective (cycleArcFrom s L)

section NeZero

variable [NeZero n]

/-! ### The two blocks around an edge

The edge type orients an edge by the linear order on `Fin n`, while the
blocking is described along the cyclic order: around the edge joining `a` to
its cyclic successor `a + 1`, the first block is the `L` sites ending at `a`
and the second is the `L` sites starting at `a + 1`.  The seam edge (between
the last and the zeroth vertex) has its endpoints in the opposite linear
order, so the two blocks are attached to the endpoints by cases on which
endpoint is the cyclic predecessor of the other. -/

/-- Every edge of the cycle graph joins a vertex to its cyclic successor, in
one of the two endpoint orders. -/
theorem cycleEdge_succ_or (hn : 3 ≤ n) (e : Edge (SimpleGraph.cycleGraph n)) :
    e.1.1 + 1 = e.1.2 ∨ e.1.2 + 1 = e.1.1 :=
  (cycleGraph_adj_iff_add_one hn).mp e.2.2

/-- The block of `L` consecutive sites on the first-endpoint side of an edge
of the cycle graph: the `L` sites ending at the first endpoint when the
second endpoint is its cyclic successor, and the `L` sites starting at the
first endpoint otherwise.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`,
via the edge blocking of the proof of Theorem 3 (lines 1475--1500). -/
def cycleEdgeRed (L : ℕ) (e : Edge (SimpleGraph.cycleGraph n)) : Finset (Fin n) :=
  if e.1.1 + 1 = e.1.2 then cycleArcTo e.1.1 L else cycleArcFrom e.1.1 L

/-- The block of `L` consecutive sites on the second-endpoint side of an edge
of the cycle graph, complementary to `cycleEdgeRed`.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`,
via the edge blocking of the proof of Theorem 3 (lines 1475--1500). -/
def cycleEdgeBlue (L : ℕ) (e : Edge (SimpleGraph.cycleGraph n)) : Finset (Fin n) :=
  if e.1.1 + 1 = e.1.2 then cycleArcFrom e.1.2 L else cycleArcTo e.1.2 L

/-- The red block when the second endpoint is the cyclic successor of the
first. -/
theorem cycleEdgeRed_of_succ {L : ℕ} {e : Edge (SimpleGraph.cycleGraph n)}
    (hsucc : e.1.1 + 1 = e.1.2) :
    cycleEdgeRed L e = cycleArcTo e.1.1 L := if_pos hsucc

/-- The blue block when the second endpoint is the cyclic successor of the
first. -/
theorem cycleEdgeBlue_of_succ {L : ℕ} {e : Edge (SimpleGraph.cycleGraph n)}
    (hsucc : e.1.1 + 1 = e.1.2) :
    cycleEdgeBlue L e = cycleArcFrom (e.1.1 + 1) L :=
  (if_pos hsucc).trans (congrArg (fun a => cycleArcFrom a L) hsucc.symm)

/-- The red block when the first endpoint is the cyclic successor of the
second. -/
theorem cycleEdgeRed_of_succ' {L : ℕ} {e : Edge (SimpleGraph.cycleGraph n)}
    (hsucc : ¬e.1.1 + 1 = e.1.2) (hsucc2 : e.1.2 + 1 = e.1.1) :
    cycleEdgeRed L e = cycleArcFrom (e.1.2 + 1) L :=
  (if_neg hsucc).trans (congrArg (fun a => cycleArcFrom a L) hsucc2.symm)

/-- The blue block when the first endpoint is the cyclic successor of the
second. -/
theorem cycleEdgeBlue_of_succ' {L : ℕ} {e : Edge (SimpleGraph.cycleGraph n)}
    (hsucc : ¬e.1.1 + 1 = e.1.2) :
    cycleEdgeBlue L e = cycleArcTo e.1.2 L := if_neg hsucc

/-- The first endpoint of an edge lies in its red block. -/
theorem left_mem_cycleEdgeRed {L : ℕ} (hL : 0 < L) (e : Edge (SimpleGraph.cycleGraph n)) :
    e.1.1 ∈ cycleEdgeRed L e := by
  unfold cycleEdgeRed
  split_ifs
  · exact last_mem_cycleArcTo hL
  · exact start_mem_cycleArcFrom hL

/-- The second endpoint of an edge lies in its blue block. -/
theorem right_mem_cycleEdgeBlue {L : ℕ} (hL : 0 < L) (e : Edge (SimpleGraph.cycleGraph n)) :
    e.1.2 ∈ cycleEdgeBlue L e := by
  unfold cycleEdgeBlue
  split_ifs
  · exact start_mem_cycleArcFrom hL
  · exact last_mem_cycleArcTo hL

/-- The red and blue blocks of an edge are disjoint on a chain of at least
`3L` sites. -/
theorem disjoint_cycleEdgeRed_cycleEdgeBlue {L : ℕ} (hL : 0 < L) (hn : 3 * L ≤ n)
    (e : Edge (SimpleGraph.cycleGraph n)) :
    Disjoint (cycleEdgeRed L e) (cycleEdgeBlue L e) := by
  have hn3 : 3 ≤ n := by omega
  by_cases hsucc : e.1.1 + 1 = e.1.2
  · rw [cycleEdgeRed_of_succ hsucc, cycleEdgeBlue_of_succ hsucc]
    exact disjoint_cycleArcTo_cycleArcFrom_add_one hL (by omega)
  · have hsucc2 := (cycleEdge_succ_or hn3 e).resolve_left hsucc
    rw [cycleEdgeRed_of_succ' hsucc hsucc2, cycleEdgeBlue_of_succ' hsucc]
    exact (disjoint_cycleArcTo_cycleArcFrom_add_one hL (by omega)).symm

/-- The union of the red and blue blocks of an edge misses the arc of the
remaining `n - 2L` consecutive sites; the complementary block is that arc. -/
theorem compl_cycleEdgeRed_union_cycleEdgeBlue {L : ℕ} (hL : 0 < L) (hn : 3 * L ≤ n)
    (e : Edge (SimpleGraph.cycleGraph n)) :
    ∃ s : Fin n,
      Finset.univ \ (cycleEdgeRed L e ∪ cycleEdgeBlue L e) = cycleArcFrom s (n - 2 * L) := by
  have hn3 : 3 ≤ n := by omega
  by_cases hsucc : e.1.1 + 1 = e.1.2
  · refine ⟨e.1.1 + 1 + ⟨L, by omega⟩, ?_⟩
    rw [cycleEdgeRed_of_succ hsucc, cycleEdgeBlue_of_succ hsucc]
    exact compl_cycleArcTo_union_cycleArcFrom_add_one hL hn
  · have hsucc2 := (cycleEdge_succ_or hn3 e).resolve_left hsucc
    refine ⟨e.1.2 + 1 + ⟨L, by omega⟩, ?_⟩
    rw [cycleEdgeRed_of_succ' hsucc hsucc2, cycleEdgeBlue_of_succ' hsucc,
      Finset.union_comm]
    exact compl_cycleArcTo_union_cycleArcFrom_add_one hL hn

variable {κ : RegionInjectivityData (Fin n)}

/-- The red block of every edge is injective under the arc-injectivity
hypotheses. -/
theorem cycleEdgeRed_injective {L : ℕ} (h : NormalCycleArcInjectivityHypotheses L κ)
    (hL : 0 < L) (hn : 3 * L ≤ n) (e : Edge (SimpleGraph.cycleGraph n)) :
    κ.IsInjective (cycleEdgeRed L e) := by
  unfold cycleEdgeRed
  split_ifs
  · exact isInjective_cycleArcTo h.arc_injective hL (by omega) _
  · exact h.arc_injective _

/-- The blue block of every edge is injective under the arc-injectivity
hypotheses. -/
theorem cycleEdgeBlue_injective {L : ℕ} (h : NormalCycleArcInjectivityHypotheses L κ)
    (hL : 0 < L) (hn : 3 * L ≤ n) (e : Edge (SimpleGraph.cycleGraph n)) :
    κ.IsInjective (cycleEdgeBlue L e) := by
  unfold cycleEdgeBlue
  split_ifs
  · exact h.arc_injective _
  · exact isInjective_cycleArcTo h.arc_injective hL (by omega) _

/-! ### The per-edge blocking datum -/

/-- The blocking of the cycle around an edge: the `L` sites on the
first-endpoint side, the `L` sites on the second-endpoint side, and the
remaining `n - 2L ≥ L` sites, each block injective, the blocks pairwise
disjoint and covering the chain.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`
("two normal MPS on `n ≥ 3L` sites with the property that blocking any `L`
consecutive sites results in an injective tensor"), realizing the blocking
into three partite injective MPS around every edge required by the theorem
labelled `normal` (lines 1576--1583). -/
def cycleEdgeBlockingData {L : ℕ} (h : NormalCycleArcInjectivityHypotheses L κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hn : 3 * L ≤ n)
    (e : Edge (SimpleGraph.cycleGraph n)) :
    NormalEdgeBlockingData κ (SimpleGraph.cycleGraph n) e where
  red := cycleEdgeRed L e
  blue := cycleEdgeBlue L e
  complement := Finset.univ \ (cycleEdgeRed L e ∪ cycleEdgeBlue L e)
  left_mem_red := left_mem_cycleEdgeRed hL e
  right_mem_blue := right_mem_cycleEdgeBlue hL e
  red_injective := cycleEdgeRed_injective h hL hn e
  blue_injective := cycleEdgeBlue_injective h hL hn e
  complement_injective := by
    obtain ⟨s, hs⟩ := compl_cycleEdgeRed_union_cycleEdgeBlue hL hn e
    rw [hs]
    exact isInjective_cycleArcFrom_of_le hUnion h.arc_injective hL (by omega) (by omega) s
  red_disjoint_blue := disjoint_cycleEdgeRed_cycleEdgeBlue hL hn e
  red_disjoint_complement :=
    Disjoint.mono_left Finset.subset_union_left Finset.sdiff_disjoint.symm
  blue_disjoint_complement :=
    Disjoint.mono_left Finset.subset_union_right Finset.sdiff_disjoint.symm
  cover_univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)

/-! ### The single red-to-blue crossing -/

/-- **The red-to-blue crossings of the cycle edge blocking are the single
distinguished edge.**  On a chain of `n ≥ 3L` sites the far ends of the two
length-`L` blocks around an edge are separated by the remaining `n - 2L ≥ L`
sites, so the only nearest-neighbour pair joining the blocks is the edge
itself.  This is the single-crossing hypothesis of the general normal PEPS
theorem.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`,
via the edge blocking of the proof of Theorem 3 (lines 1475--1500). -/
theorem isCrossingEdge_cycleEdge_iff {d : ℕ} (A : Tensor (SimpleGraph.cycleGraph n) d)
    {L : ℕ} (hL : 0 < L) (hn : 3 * L ≤ n) (e g : Edge (SimpleGraph.cycleGraph n)) :
    IsCrossingEdge (G := SimpleGraph.cycleGraph n) A
        (cycleEdgeRed L e) (cycleEdgeBlue L e) g ↔ g = e := by
  have hn3 : 3 ≤ n := by omega
  have hdisj := disjoint_cycleEdgeRed_cycleEdgeBlue hL hn e
  constructor
  · rintro ⟨hbR, hbB⟩
    -- One endpoint of `g` lies in the red block and the other in the blue block.
    have hsplit : (g.1.1 ∈ cycleEdgeRed L e ∧ g.1.2 ∈ cycleEdgeBlue L e) ∨
        (g.1.2 ∈ cycleEdgeRed L e ∧ g.1.1 ∈ cycleEdgeBlue L e) := by
      rcases hbR with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hbB with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
        · exact absurd hb1 (Finset.disjoint_left.mp hdisj h1)
        · exact Or.inl ⟨h1, hb2⟩
      · rcases hbB with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
        · exact Or.inr ⟨h2, hb1⟩
        · exact absurd hb2 (Finset.disjoint_left.mp hdisj h2)
    have hadj : g.1.1 + 1 = g.1.2 ∨ g.1.2 + 1 = g.1.1 :=
      (cycleGraph_adj_iff_add_one hn3).mp g.2.2
    by_cases hsucc : e.1.1 + 1 = e.1.2
    · rw [cycleEdgeRed_of_succ hsucc, cycleEdgeBlue_of_succ hsucc] at hsplit
      rcases hsplit with ⟨hu, hw⟩ | ⟨hu, hw⟩
      · obtain ⟨he1, he2⟩ :=
          eq_of_adj_mem_cycleArcTo_mem_cycleArcFrom hL hn hadj hu hw
        exact Subtype.ext (Prod.ext he1 (he2.trans hsucc))
      · obtain ⟨he1, he2⟩ :=
          eq_of_adj_mem_cycleArcTo_mem_cycleArcFrom hL hn (Or.symm hadj) hu hw
        -- The crossed orientation contradicts the ordered-endpoint convention.
        exfalso
        have hlt := g.2.1
        rw [he1, he2, hsucc] at hlt
        exact lt_asymm e.2.1 hlt
    · have hsucc2 := (cycleEdge_succ_or hn3 e).resolve_left hsucc
      rw [cycleEdgeRed_of_succ' hsucc hsucc2, cycleEdgeBlue_of_succ' hsucc] at hsplit
      rcases hsplit with ⟨hu, hw⟩ | ⟨hu, hw⟩
      · obtain ⟨he1, he2⟩ :=
          eq_of_adj_mem_cycleArcTo_mem_cycleArcFrom hL hn (Or.symm hadj) hw hu
        exact Subtype.ext (Prod.ext (he2.trans hsucc2) he1)
      · obtain ⟨he1, he2⟩ :=
          eq_of_adj_mem_cycleArcTo_mem_cycleArcFrom hL hn hadj hw hu
        -- The crossed orientation contradicts the ordered-endpoint convention.
        exfalso
        have hlt := g.2.1
        rw [he1, he2, hsucc2] at hlt
        exact lt_asymm e.2.1 hlt
  · rintro rfl
    have h1 := left_mem_cycleEdgeRed (n := n) hL g
    have h2 := right_mem_cycleEdgeBlue (n := n) hL g
    exact ⟨Or.inl ⟨h1, Finset.disjoint_right.mp hdisj h2⟩,
      Or.inr ⟨Finset.disjoint_left.mp hdisj h1, h2⟩⟩

/-! ### The one-site comparison regions -/

/-- The one-site comparison regions on the cycle: at every site `v`, the
`L + 1` sites starting at `v` and the `L` sites starting at `v + 1` are
injective regions with injective complements differing exactly at `v`.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex` ("for every site, there
are injective regions with their complements also being injective that
differ only in the given site"), realized on the chain of the first
corollary (lines 1585--1622) by blocks of consecutive sites. -/
def cycleOneSiteSeparation {L : ℕ} (h : NormalCycleArcInjectivityHypotheses L κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hn : 3 * L ≤ n) :
    NormalOneSiteSeparationHypotheses κ where
  withSite v := cycleArcFrom v (L + 1)
  withoutSite v := cycleArcFrom (v + 1) L
  withSite_injective v :=
    isInjective_cycleArcFrom_of_le hUnion h.arc_injective hL (by omega) (by omega) v
  withoutSite_injective v := h.arc_injective (v + 1)
  withSite_complement_injective v := by
    simp only [regionComplement]
    rw [compl_cycleArcFrom (show L + 1 < n by omega)]
    exact isInjective_cycleArcFrom_of_le hUnion h.arc_injective hL (by omega) (by omega) _
  withoutSite_complement_injective v := by
    simp only [regionComplement]
    rw [compl_cycleArcFrom (show L < n by omega)]
    exact isInjective_cycleArcFrom_of_le hUnion h.arc_injective hL (by omega) (by omega) _
  site_mem_withSite v := start_mem_cycleArcFrom (by omega)
  site_notMem_withoutSite v := self_notMem_cycleArcFrom_add_one hL (by omega)
  agree_away v w hvw := mem_cycleArcFrom_succ_iff_of_ne (by omega) hvw

/-! ### The assembled blocking hypotheses -/

/-- The blocking hypotheses of the general normal PEPS theorem on the cycle
graph, assembled from the arc-injectivity hypotheses of the source corollary:
the per-edge three-block chains and the one-site comparison regions.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`,
supplying the hypotheses of the theorem labelled `normal` (lines 1576--1583)
on the closed chain. -/
def cycleNormalPEPSBlockingHypotheses {L : ℕ} (h : NormalCycleArcInjectivityHypotheses L κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hn : 3 * L ≤ n) :
    NormalPEPSBlockingHypotheses κ (SimpleGraph.cycleGraph n) where
  edgeBlocking :=
    NormalEdgeBlockingHypotheses.ofBlockingData fun e => cycleEdgeBlockingData h hUnion hL hn e
  oneSiteSeparation := cycleOneSiteSeparation h hUnion hL hn

@[simp] theorem cycleNormalPEPSBlockingHypotheses_red {L : ℕ}
    (h : NormalCycleArcInjectivityHypotheses L κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hn : 3 * L ≤ n)
    (e : Edge (SimpleGraph.cycleGraph n)) :
    (cycleNormalPEPSBlockingHypotheses h hUnion hL hn).edgeBlocking.red e =
      cycleEdgeRed L e := rfl

@[simp] theorem cycleNormalPEPSBlockingHypotheses_blue {L : ℕ}
    (h : NormalCycleArcInjectivityHypotheses L κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hn : 3 * L ≤ n)
    (e : Edge (SimpleGraph.cycleGraph n)) :
    (cycleNormalPEPSBlockingHypotheses h hUnion hL hn).edgeBlocking.blue e =
      cycleEdgeBlue L e := rfl

end NeZero

end PEPS
end TNLean
