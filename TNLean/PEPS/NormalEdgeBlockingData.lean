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
  /-- The first injective block around the edge. -/
  red : Finset V
  /-- The second injective block around the edge. -/
  blue : Finset V
  /-- The complementary injective block around the edge. -/
  complement : Finset V
  /-- The left endpoint of the edge lies in the red block. -/
  left_mem_red : e.1.1 ∈ red
  /-- The right endpoint of the edge lies in the blue block. -/
  right_mem_blue : e.1.2 ∈ blue
  /-- The red block is injective. -/
  red_injective : ι.IsInjective red
  /-- The blue block is injective. -/
  blue_injective : ι.IsInjective blue
  /-- The complementary block is injective. -/
  complement_injective : ι.IsInjective complement
  /-- The red and blue blocks are disjoint. -/
  red_disjoint_blue : Disjoint red blue
  /-- The red and complementary blocks are disjoint. -/
  red_disjoint_complement : Disjoint red complement
  /-- The blue and complementary blocks are disjoint. -/
  blue_disjoint_complement : Disjoint blue complement
  /-- The three edge-centred blocks cover the vertex set. -/
  cover_univ : red ∪ blue ∪ complement = Finset.univ

namespace NormalEdgeBlockingData

variable {ι}

/-- The one-edge blocking datum supplies the three injective regions used in
the associated three-site chain.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem injective_chain {G : SimpleGraph V} {e : Edge G}
    (d : NormalEdgeBlockingData ι G e) :
    ι.IsInjective d.red ∧ ι.IsInjective d.blue ∧ ι.IsInjective d.complement :=
  ⟨d.red_injective, d.blue_injective, d.complement_injective⟩

/-- The one-edge blocking datum records endpoint membership, pairwise
disjointness, and coverage by the three regions.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem endpoint_disjoint_cover {G : SimpleGraph V} {e : Edge G}
    (d : NormalEdgeBlockingData ι G e) :
    e.1.1 ∈ d.red ∧ e.1.2 ∈ d.blue ∧ Disjoint d.red d.blue ∧
      Disjoint d.red d.complement ∧ Disjoint d.blue d.complement ∧
      d.red ∪ d.blue ∪ d.complement = Finset.univ :=
  ⟨d.left_mem_red, d.right_mem_blue, d.red_disjoint_blue,
    d.red_disjoint_complement, d.blue_disjoint_complement, d.cover_univ⟩

/-- For one edge, the red, blue, and complementary regions contain the
corresponding endpoints, are injective, are pairwise disjoint, and cover the
vertex set.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem endpoint_injective_disjoint_cover {G : SimpleGraph V} {e : Edge G}
    (d : NormalEdgeBlockingData ι G e) :
    e.1.1 ∈ d.red ∧ e.1.2 ∈ d.blue ∧
      ι.IsInjective d.red ∧ ι.IsInjective d.blue ∧ ι.IsInjective d.complement ∧
      Disjoint d.red d.blue ∧ Disjoint d.red d.complement ∧
      Disjoint d.blue d.complement ∧ d.red ∪ d.blue ∪ d.complement = Finset.univ :=
  ⟨d.left_mem_red, d.right_mem_blue, d.red_injective, d.blue_injective,
    d.complement_injective, d.red_disjoint_blue, d.red_disjoint_complement,
    d.blue_disjoint_complement, d.cover_univ⟩

end NormalEdgeBlockingData

/-- Edge-centred blocking into three injective regions.

For every edge, the normal PEPS proof blocks the network into a red region, a
blue region, and the complementary region. The edge endpoints lie in the red
and blue regions respectively, the three regions are pairwise disjoint, their
union is the whole vertex set, and each region is injective.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
structure NormalEdgeBlockingHypotheses (G : SimpleGraph V) where
  /-- The one-edge blocking datum attached to each edge. -/
  blockingData : ∀ e : Edge G, NormalEdgeBlockingData ι G e

namespace NormalEdgeBlockingHypotheses

variable {ι}

/-- The first injective block around each edge. -/
def red (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) : Finset V :=
  (h.blockingData e).red

/-- The second injective block around each edge. -/
def blue (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) : Finset V :=
  (h.blockingData e).blue

/-- The complementary injective block around each edge. -/
def complement (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) : Finset V :=
  (h.blockingData e).complement

/-- The left endpoint of the edge lies in the red block. -/
theorem left_mem_red (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    e.1.1 ∈ h.red e :=
  (h.blockingData e).left_mem_red

/-- The right endpoint of the edge lies in the blue block. -/
theorem right_mem_blue (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    e.1.2 ∈ h.blue e :=
  (h.blockingData e).right_mem_blue

/-- The red block is injective. -/
theorem red_injective (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    ι.IsInjective (h.red e) :=
  (h.blockingData e).red_injective

/-- The blue block is injective. -/
theorem blue_injective (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    ι.IsInjective (h.blue e) :=
  (h.blockingData e).blue_injective

/-- The complementary block is injective. -/
theorem complement_injective (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    ι.IsInjective (h.complement e) :=
  (h.blockingData e).complement_injective

/-- The red and blue blocks are disjoint. -/
theorem red_disjoint_blue (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    Disjoint (h.red e) (h.blue e) :=
  (h.blockingData e).red_disjoint_blue

/-- The red and complementary blocks are disjoint. -/
theorem red_disjoint_complement (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    Disjoint (h.red e) (h.complement e) :=
  (h.blockingData e).red_disjoint_complement

/-- The blue and complementary blocks are disjoint. -/
theorem blue_disjoint_complement (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    Disjoint (h.blue e) (h.complement e) :=
  (h.blockingData e).blue_disjoint_complement

/-- The three edge-centred blocks cover the vertex set. -/
theorem cover_univ (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    h.red e ∪ h.blue e ∪ h.complement e = Finset.univ :=
  (h.blockingData e).cover_univ

/-- Assemble edge-centred blocking hypotheses from one-edge blocking data
available for every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the proof blocks around every edge before applying the injective
three-site comparison. -/
def ofBlockingData (data : ∀ e : Edge G, NormalEdgeBlockingData ι G e) :
    NormalEdgeBlockingHypotheses ι G where
  blockingData := data

/-- Recovering the one-edge datum from hypotheses assembled from one-edge data
returns the datum supplied at that edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
@[simp] theorem ofBlockingData_blockingData
    (data : ∀ e : Edge G, NormalEdgeBlockingData ι G e) (e : Edge G) :
    (ofBlockingData data).blockingData e = data e :=
  rfl

/-- The edge-centred blocking supplies a three-region injective chain at every
edge. -/
theorem injective_chain_at_edge (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    ι.IsInjective (h.red e) ∧ ι.IsInjective (h.blue e) ∧
      ι.IsInjective (h.complement e) :=
  (h.blockingData e).injective_chain

/-- At every edge, the edge-centred blocking records endpoint membership,
pairwise disjointness, and coverage by the three regions.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem endpoint_disjoint_cover_at_edge
    (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    e.1.1 ∈ h.red e ∧ e.1.2 ∈ h.blue e ∧ Disjoint (h.red e) (h.blue e) ∧
      Disjoint (h.red e) (h.complement e) ∧
      Disjoint (h.blue e) (h.complement e) ∧
      h.red e ∪ h.blue e ∪ h.complement e = Finset.univ :=
  (h.blockingData e).endpoint_disjoint_cover

end NormalEdgeBlockingHypotheses

end PEPS
end TNLean
