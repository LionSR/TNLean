import TNLean.PEPS.RegionTransport
import TNLean.PEPS.RegionBlock.Insertion
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap5

/-!
# Covariance of the region-inserted coefficient under a graph isomorphism

A graph isomorphism `φ : G ≃g G'` carries the region-inserted coefficient of a tensor `A`
over a region `R` to the region-inserted coefficient of the transported tensor `A.transport φ`
over the image region `Region.map φ R`, with the inserted matrix carried to the image bond, the
boundary edge to its image, and the region/complement physical configurations relabelled by the
vertex bijection (`regionInsertedCoeff_transport`).

The region-inserted coefficient is the double boundary-configuration sum coupling `R` and its
set complement through a single matrix inserted on one boundary edge `f`.  The blocked-region
weight transports (`regionBlockedWeight_transport`), the boundary configurations reindex by the
edge action (`regionBoundaryConfigMapEquiv`), and the `SameAwayFromBond` coupling is preserved by
that reindex, so the whole double sum carries across.  No endpoint orientation enters: the
coefficient inserts the matrix between the two boundary configurations' single values on the
boundary edge, with no reference to which endpoint lies in `R`.

This is the missing covariance of obligation 6 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`: together with the transport of the blocked
weights it makes the per-edge transfer maps covariant under translation on the torus.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines
  1407--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V W : Type*} [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W]
  {G : SimpleGraph V} {G' : SimpleGraph W} {d : ℕ}
variable [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-! ### The image boundary edge -/

/-- The image of a boundary edge of `R` under the edge action of `φ`: a boundary edge of the
image region whose underlying edge is `Edge.map φ f.1`.  This is the inverse direction of the
boundary-edge reindexing `regionBoundaryEdgeMapEquiv`. -/
def boundaryEdgeMap (φ : G ≃g G') (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    {f : Edge G' // IsRegionBoundaryEdge (G := G') (Region.map φ R) f} :=
  (regionBoundaryEdgeMapEquiv φ R).symm f

omit [Fintype V] [Fintype W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
@[simp] theorem boundaryEdgeMap_coe (φ : G ≃g G') (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    (boundaryEdgeMap φ R f).1 = Edge.map φ f.1 := rfl

omit [Fintype V] [Fintype W] in
/-- The bond dimension of `A.transport φ` at the image boundary edge equals the bond dimension of
`A` at the original boundary edge. -/
theorem transport_bondDim_boundaryEdgeMap (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    (A.transport φ).bondDim (boundaryEdgeMap φ R f).1 = A.bondDim f.1 := by
  rw [boundaryEdgeMap_coe, Tensor.transport_bondDim, Edge.map_symm_map]

/-! ### Transport of the complement-side blocked weight

The region-inserted coefficient contracts the set complement `univ \ R` on the second factor.
Under transport, the image coefficient contracts `univ \ Region.map φ R`, while the transport of
the original complement weight lives over `Region.map φ (univ \ R)`.  These two regions agree
(`Region_map_compl`), and the complement boundary configurations match across the region equality,
so the image complement weight equals the original complement weight. -/


/-- The image complement boundary configuration, read on `univ \ Region.map φ R`, agrees across
the region equality `Region.map φ (univ \ R) = univ \ Region.map φ R` with the transport of the
original complement boundary configuration on `Region.map φ (univ \ R)`. -/
theorem regionComplementBoundaryConfig_transport (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (ν : RegionBoundaryConfig (G := G) A R) :
    regionComplementBoundaryConfig (G := G') (A.transport φ) (Region.map φ R)
        (regionBoundaryConfigMap A φ R ν) =
      regionBoundaryConfigCongr (A := A.transport φ) (Region_map_compl φ R)
        (regionBoundaryConfigMap A φ (Finset.univ \ R)
          (regionComplementBoundaryConfig (G := G) A R ν)) := by
  funext f
  rw [regionBoundaryConfigCongr_apply]
  -- After the congr rewrite both sides read `ν` on the same reindexed boundary edge.
  rfl

/-- **Transport of the complement-side blocked weight.**

The blocked weight of `A.transport φ` over the set complement `univ \ Region.map φ R`, at the
image complement boundary configuration and the image complement physical configuration, equals
the blocked weight of `A` over `univ \ R`.  This bridges the region equality
`Region.map φ (univ \ R) = univ \ Region.map φ R` (`Region_map_compl`) and then applies the
blocked-weight transport (`regionBlockedWeight_transport`). -/
theorem regionComplementWeight_transport (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (ν : RegionBoundaryConfig (G := G) A R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionBlockedWeight (G := G') (A.transport φ) (Finset.univ \ Region.map φ R)
        (regionComplementBoundaryConfig (G := G') (A.transport φ) (Region.map φ R)
          (regionBoundaryConfigMap A φ R ν))
        (regionPhysicalConfigCongr (d := d) (Region_map_compl φ R)
          (regionPhysicalConfigMap φ (Finset.univ \ R) τ)) =
      regionBlockedWeight (G := G) A (Finset.univ \ R)
        (regionComplementBoundaryConfig (G := G) A R ν) τ := by
  -- Bridge the region equality, then apply the blocked-weight transport for `univ \ R`.
  rw [regionComplementBoundaryConfig_transport,
    ← regionBlockedWeight_congr (A := A.transport φ) (Region_map_compl φ R)
      (regionBoundaryConfigMap A φ (Finset.univ \ R)
        (regionComplementBoundaryConfig (G := G) A R ν))
      (regionPhysicalConfigMap φ (Finset.univ \ R) τ),
    regionBlockedWeight_transport A φ (Finset.univ \ R)
      (regionComplementBoundaryConfig (G := G) A R ν) τ]

end PEPS
end TNLean
