import TNLean.PEPS.Defs
import TNLean.PEPS.InjectiveRegion

/-!
# One-edge blocking data for the normal PEPS proof

This file records the one-edge red/blue/complement datum used before the
normal square-lattice construction is translated around every edge.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3]
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable (ι : RegionInjectivityData V)

/-- Red, blue, and complementary blocking data for one fixed edge.

This is the one-edge form of `NormalEdgeBlockingHypotheses`, used before the
normalized edge construction is translated around the full lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
structure NormalEdgeBlockingData (G : SimpleGraph V) (e : Edge G) where
  red : Finset V
  blue : Finset V
  complement : Finset V
  left_mem_red : e.1.1 ∈ red
  right_mem_blue : e.1.2 ∈ blue
  red_injective : ι.IsInjective red
  blue_injective : ι.IsInjective blue
  complement_injective : ι.IsInjective complement
  red_disjoint_blue : Disjoint red blue
  red_disjoint_complement : Disjoint red complement
  blue_disjoint_complement : Disjoint blue complement
  cover_univ : red ∪ blue ∪ complement = Finset.univ

/-- Edge-centred blocking into three injective regions.

For every edge, the normal PEPS proof blocks the network into a red region, a
blue region, and the complementary region. The edge endpoints lie in the red
and blue regions respectively, the three regions are pairwise disjoint, their
union is the whole vertex set, and each region is injective.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
structure NormalEdgeBlockingHypotheses (G : SimpleGraph V) where
  /-- The first injective block around each edge. -/
  red : Edge G → Finset V
  /-- The second injective block around each edge. -/
  blue : Edge G → Finset V
  /-- The complementary injective block around each edge. -/
  complement : Edge G → Finset V
  /-- The left endpoint of the edge lies in the red block. -/
  left_mem_red : ∀ e : Edge G, e.1.1 ∈ red e
  /-- The right endpoint of the edge lies in the blue block. -/
  right_mem_blue : ∀ e : Edge G, e.1.2 ∈ blue e
  /-- The red block is injective. -/
  red_injective : ∀ e : Edge G, ι.IsInjective (red e)
  /-- The blue block is injective. -/
  blue_injective : ∀ e : Edge G, ι.IsInjective (blue e)
  /-- The complementary block is injective. -/
  complement_injective : ∀ e : Edge G, ι.IsInjective (complement e)
  /-- The red and blue blocks are disjoint. -/
  red_disjoint_blue : ∀ e : Edge G, Disjoint (red e) (blue e)
  /-- The red and complementary blocks are disjoint. -/
  red_disjoint_complement : ∀ e : Edge G, Disjoint (red e) (complement e)
  /-- The blue and complementary blocks are disjoint. -/
  blue_disjoint_complement : ∀ e : Edge G, Disjoint (blue e) (complement e)
  /-- The three edge-centred blocks cover the vertex set. -/
  cover_univ : ∀ e : Edge G, red e ∪ blue e ∪ complement e = Finset.univ

namespace NormalEdgeBlockingHypotheses

variable {ι}

/-- The one-edge blocking data supplied by edge-centred blocking hypotheses. -/
def blockingData (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    NormalEdgeBlockingData ι G e where
  red := h.red e
  blue := h.blue e
  complement := h.complement e
  left_mem_red := h.left_mem_red e
  right_mem_blue := h.right_mem_blue e
  red_injective := h.red_injective e
  blue_injective := h.blue_injective e
  complement_injective := h.complement_injective e
  red_disjoint_blue := h.red_disjoint_blue e
  red_disjoint_complement := h.red_disjoint_complement e
  blue_disjoint_complement := h.blue_disjoint_complement e
  cover_univ := h.cover_univ e

/-- Assemble edge-centred blocking hypotheses from one-edge blocking data
available for every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the proof blocks around every edge before applying the injective
three-site comparison. -/
def ofBlockingData (data : ∀ e : Edge G, NormalEdgeBlockingData ι G e) :
    NormalEdgeBlockingHypotheses ι G where
  red e := (data e).red
  blue e := (data e).blue
  complement e := (data e).complement
  left_mem_red e := (data e).left_mem_red
  right_mem_blue e := (data e).right_mem_blue
  red_injective e := (data e).red_injective
  blue_injective e := (data e).blue_injective
  complement_injective e := (data e).complement_injective
  red_disjoint_blue e := (data e).red_disjoint_blue
  red_disjoint_complement e := (data e).red_disjoint_complement
  blue_disjoint_complement e := (data e).blue_disjoint_complement
  cover_univ e := (data e).cover_univ

/-- The edge-centred blocking supplies a three-region injective chain at every
edge. -/
theorem injective_chain_at_edge (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    ι.IsInjective (h.red e) ∧ ι.IsInjective (h.blue e) ∧
      ι.IsInjective (h.complement e) :=
  ⟨h.red_injective e, h.blue_injective e, h.complement_injective e⟩

end NormalEdgeBlockingHypotheses

end PEPS
end TNLean
