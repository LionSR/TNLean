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

variable {A : Tensor G d}

/-! ### The crossing-triple reindexing of coarse virtual configurations

The bond models of a coherent frame are equivalences between the three coarse
super-bonds and the three original inter-region crossing configurations. Since a
coarse virtual configuration is determined by its three super-bond values, the
bond models assemble into one product equivalence between coarse virtual
configurations and triples of crossing configurations. This is the change of
variables that turns the triple sum over coarse configurations into a sum over the
original crossing data the merge collapse contracts. -/

/-- **The crossing-triple reindexing.** The product equivalence between coarse
virtual configurations and triples of original crossing configurations, one per
coarse super-edge, assembled from the three bond models. -/
def crossingTripleEquiv (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) :
    VirtualConfig (F.frame.coarseTensor) ≃
      (CrossingConfig (G := G) A F.frame.red F.frame.blue ×
        CrossingConfig (G := G) A F.frame.red F.frame.complement ×
        CrossingConfig (G := G) A F.frame.blue F.frame.complement) where
  toFun η := (F.bondModel coarseEdgeRB (η coarseEdgeRB),
              F.bondModel coarseEdgeRC (η coarseEdgeRC),
              F.bondModel coarseEdgeBC (η coarseEdgeBC))
  invFun t := fun f =>
    if h : f = coarseEdgeRB then h ▸ (F.bondModel coarseEdgeRB).symm t.1
    else if h2 : f = coarseEdgeRC then h2 ▸ (F.bondModel coarseEdgeRC).symm t.2.1
    else if h3 : f = coarseEdgeBC then h3 ▸ (F.bondModel coarseEdgeBC).symm t.2.2
    else absurd ((coarse_edge_cases f).resolve_left h |>.resolve_left h2) h3
  left_inv η := by
    funext f
    dsimp only
    rcases coarse_edge_cases f with h | h | h <;> subst h
    · rw [dif_pos rfl]; exact (F.bondModel coarseEdgeRB).symm_apply_apply _
    · rw [dif_neg (by decide), dif_pos rfl]
      exact (F.bondModel coarseEdgeRC).symm_apply_apply _
    · rw [dif_neg (by decide), dif_neg (by decide), dif_pos rfl]
      exact (F.bondModel coarseEdgeBC).symm_apply_apply _
  right_inv t := by
    obtain ⟨a, b, c⟩ := t
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · dsimp only; rw [dif_pos rfl]; exact (F.bondModel coarseEdgeRB).apply_symm_apply _
    · dsimp only; rw [dif_neg (show coarseEdgeRC ≠ coarseEdgeRB by decide), dif_pos rfl]
      exact (F.bondModel coarseEdgeRC).apply_symm_apply _
    · dsimp only
      rw [dif_neg (show coarseEdgeBC ≠ coarseEdgeRB by decide),
        dif_neg (show coarseEdgeBC ≠ coarseEdgeRC by decide), dif_pos rfl]
      exact (F.bondModel coarseEdgeBC).apply_symm_apply _

@[simp] theorem crossingTripleEquiv_apply (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (η : VirtualConfig (F.frame.coarseTensor)) :
    crossingTripleEquiv F η =
      (F.bondModel coarseEdgeRB (η coarseEdgeRB),
        F.bondModel coarseEdgeRC (η coarseEdgeRC),
        F.bondModel coarseEdgeBC (η coarseEdgeBC)) := rfl

end PEPS
end TNLean
