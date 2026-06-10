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

end PEPS
end TNLean
