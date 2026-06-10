import TNLean.PEPS.RegionBlock.CoarseThreeSite3

/-!
# The global fiber-collapse bijection for the normal PEPS theorem

The coarse three-site tensor of `TNLean.PEPS.RegionBlock.CoarseThreeSite` has its
closed-state coefficient written, through the coherent bond models of
`TNLean.PEPS.RegionBlock.CoarseThreeSite2`, as a sum over coarse virtual
configurations of a product of three original blocked-region weights
(`stateCoeff_coarseTensor_eq_threeRegionSum`), and the region boundary
configurations induced by a coarse configuration are read off the bond models
(`TNLean.PEPS.RegionBlock.CoarseThreeSite3`). This file collapses that triple sum
to a constant times the original closed-state coefficient.

The route mirrors the landed two-block collapse
`TNLean.PEPS.stateCoeff_eq_regionComplement`: a coarse virtual configuration `η`
together with the three constrained inner sums of the blocked-region weights is
reindexed by a triple of global virtual configurations of the original tensor
`(ζ_red, ζ_blue, ζ_compl)` whose region boundary labels agree on the shared
crossing edges; merging that triple into one global configuration (the red-incident
edges read `ζ_red`, the remaining blue-incident edges read `ζ_blue`, the rest read
`ζ_compl`) collapses the sum to the closed-state coefficient with the three
regions' interior bond products as multiplicity.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1205--1210 (the one-region-against-complement gluing) and
  1449--1500 (the blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Enumeration of the coarse super-edges

The coarse graph is the complete graph on `Fin 3`; its edge set is exactly the
three super-edges `r-b`, `r-c`, `b-c`. A coarse virtual configuration is therefore
determined by its three super-bond values, the fact the reindexing of the triple
sum consumes. -/

/-- Every super-edge of the coarse graph is one of the three named super-edges. -/
theorem coarse_edge_cases (f : Edge coarseGraph) :
    f = coarseEdgeRB ∨ f = coarseEdgeRC ∨ f = coarseEdgeBC := by
  revert f; decide

/-- A coarse virtual configuration is determined by its three super-bond values. -/
theorem coarse_virtualConfig_ext {A : Tensor G d}
    (F : CoarseBlockingFrame (G := G) (d := d) A)
    {η η' : VirtualConfig (F.coarseTensor)}
    (hrb : η coarseEdgeRB = η' coarseEdgeRB)
    (hrc : η coarseEdgeRC = η' coarseEdgeRC)
    (hbc : η coarseEdgeBC = η' coarseEdgeBC) : η = η' := by
  funext f
  rcases coarse_edge_cases f with h | h | h <;> subst h <;> assumption

end PEPS
end TNLean
