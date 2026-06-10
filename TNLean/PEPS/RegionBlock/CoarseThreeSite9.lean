import TNLean.PEPS.RegionBlock.CoarseThreeSite8

/-!
# The relaxed-triple merge collapse for the normal PEPS theorem

The relaxed-triple reindexing `TNLean.PEPS.mCoupledThreeRegionSum_eq_relaxedTripleSum` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite7` writes the coarse edge-inserted coefficient at
the `r-b` super-bond as a sum over triples of global virtual configurations agreeing away
from the red-to-blue crossings, with the bond-model-conjugated matrix coupling the two
red-to-blue crossing labels. This file collapses that sum to a constant times the
whole-bundle red inserted coefficient `TNLean.PEPS.redBundleInsertedCoeff` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite6`, the matrix-carrying analogue of the
closed-state collapse `TNLean.PEPS.agreeingTripleSum_collapse`.

The collapse is two-sided: the red configuration merges into the red boundary index `μ` of
the whole-bundle red inserted coefficient, while the blue and complement configurations
(agreeing on the blue-to-complement crossings) merge into the host boundary index `ν` over
`univ \ red`. The bond-model-conjugated matrix couples `μ` and `ν` through their
red-to-blue crossing labels.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 254--583 (the injective three-site comparison) and 1205--1210,
  1449--1500 (the blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### The red-to-blue crossing label factors through the red boundary label

The bond-model-conjugated matrix in the relaxed-triple sum reads a global configuration only
through its red-to-blue crossing label, which is the red-to-blue crossing label of the
configuration's red boundary label. -/

omit [Fintype V] in
/-- The red-to-blue crossing label of a global configuration is the red-to-blue crossing
label of its red boundary label. -/
theorem crossingLabel_eq_redBoundaryRBCrossing (red blue : Finset V) (ζ : VirtualConfig A) :
    crossingLabel (G := G) A red blue ζ =
      redBoundaryRBCrossing (G := G) A red blue (regionBoundaryLabel (G := G) A red ζ) := by
  funext g
  rw [crossingLabel_apply, redBoundaryRBCrossing_apply, regionBoundaryLabel_apply]

variable [DecidableEq V]

/-! ### Geometric classification of red boundary crossings

Under the partition, a red boundary edge crosses to the blue region or to the complement.
A red-to-complement crossing edge is incident to the complement block, while a red-to-blue
crossing edge is not: its endpoints lie in the red and blue blocks, both disjoint from the
complement. These classify how the host-side merge along the complement reads each crossing
edge. -/

/-- A red-to-complement crossing edge is incident to the complement block. -/
theorem isRegionIncidentEdge_complement_of_crossing_rc
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {g : Edge G} (hg : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g) :
    IsRegionIncidentEdge (G := G) F.frame.complement g :=
  isRegionBoundaryEdge_touches (G := G) F.frame.complement hg.2

/-- A red-to-blue crossing edge is not incident to the complement block: its two endpoints
lie one in the red block and one in the blue block, both disjoint from the complement. -/
theorem not_isRegionIncidentEdge_complement_of_crossing_rb
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    {g : Edge G} (hg : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g) :
    ¬ IsRegionIncidentEdge (G := G) F.frame.complement g := by
  -- The red-to-blue crossing edge has, on each endpoint, a red and a blue boundary
  -- condition; the two combine to place each endpoint in red or in blue.
  have hcompl : ∀ v : V, v ∈ F.frame.red ∨ v ∈ F.frame.blue → v ∉ F.frame.complement := by
    rintro v (hr | hb) hc
    · exact (Finset.disjoint_left.mp hP.red_disjoint_complement) hr hc
    · exact (Finset.disjoint_left.mp hP.blue_disjoint_complement) hb hc
  rcases hg.1 with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ <;> rcases hg.2 with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · -- g.1.1 ∈ red, g.1.1 ∈ blue: impossible.
    exact absurd hb1 ((Finset.disjoint_left.mp hP.red_disjoint_blue) hr1)
  · -- g.1.1 ∈ red, g.1.2 ∈ blue.
    rintro (hc | hc)
    · exact hcompl _ (Or.inl hr1) hc
    · exact hcompl _ (Or.inr hb2) hc
  · -- g.1.2 ∈ red, g.1.1 ∈ blue.
    rintro (hc | hc)
    · exact hcompl _ (Or.inr hb1) hc
    · exact hcompl _ (Or.inl hr2) hc
  · -- g.1.2 ∈ red, g.1.2 ∈ blue: impossible.
    exact absurd hb2 ((Finset.disjoint_left.mp hP.red_disjoint_blue) hr2)

/-! ### The host merge of a relaxed triple's blue and complement configurations

The blue and complement configurations of a relaxed triple, agreeing on the
blue-to-complement crossings, merge into one host configuration over `univ \ red`: the
complement-incident edges read the complement configuration, the remaining edges the blue
configuration. The host vertex product of the merge reads the blue product against the
complement product, and the merge reads the original blue and complement configurations on
the host boundary through the red-to-blue and red-to-complement crossings respectively. -/

/-- The host configuration merging a relaxed triple's complement configuration `ζc` (on the
complement-incident edges) with its blue configuration `ζb` (elsewhere). This is the
complement-side `regionMerge` of the pair `(ζc, ζb)`. -/
noncomputable def hostMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζb ζc : VirtualConfig A) : VirtualConfig A :=
  regionMerge (G := G) A F.frame.complement (ζc, ζb)

omit [DecidableEq V] in
/-- The host merge reads the complement configuration on a complement-incident edge. -/
theorem hostMerge_complement (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {ζb ζc : VirtualConfig A} {e : Edge G}
    (he : IsRegionIncidentEdge (G := G) F.frame.complement e) :
    hostMerge F ζb ζc e = ζc e := by
  rw [hostMerge, regionMerge, if_pos he]

omit [DecidableEq V] in
/-- The host merge reads the blue configuration on an edge not incident to the complement. -/
theorem hostMerge_not_complement (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {ζb ζc : VirtualConfig A} {e : Edge G}
    (he : ¬ IsRegionIncidentEdge (G := G) F.frame.complement e) :
    hostMerge F ζb ζc e = ζb e := by
  rw [hostMerge, regionMerge, if_neg he]

end PEPS
end TNLean
