import TNLean.PEPS.RegionBlock.Recovery11

/-!
# Region physical-to-virtual recovery: the block-endpoint inversion (region-injective)

This file ports the block-endpoint inversion of the region resonate step to the
**region-injective** regime, with the blocked-region left inverses of `R` and of
its set complement `univ \ R` as the two inversion tools, and *without* assuming
single-vertex injectivity `IsVertexInjective`. It is the region-granularity port
of `resonate_invert_right_endpoint` (`TNLean.PEPS.InsertionRealization`) and the
first half of the open obligation of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

The contributions here are non-circular and use only blocked-region injectivity:

* `regionComplementRow_eq_regionInsertionOp` reads the explicit complement row of a
  second-tensor matrix `N` as the second tensor's own in-region endpoint operator of
  `N.transpose` against the second tensor's region weight vectors at the endpoint
  leg. This is `region_innerSum_eq_realized` (`TNLean.PEPS.RegionBlock.Recovery2`)
  packaged for the complement row of `TNLean.PEPS.RegionBlock.Recovery7`.

* `coeffTransfer_of_endpointOp_eq` reduces the **coefficient transfer** (matching the
  region-inserted coefficients of `A` and `B`) to the agreement of the two in-region
  endpoint operators on the second tensor's region weight vectors at the endpoint
  leg. The reduction inverts the complement block through the blocked-region left
  inverse `regionBlockedLeftInverse B (univ \ R) hCB` and is exactly the
  block-granularity form of inverting the second tensor's complement away from the
  in-region endpoint. It uses no single-vertex spanning.

These are the region-injective replacements for the steps that
`TNLean.PEPS.RegionBlock.Recovery9`/`Recovery10`/`Recovery11` performed with the
single-vertex realization (which needs `IsVertexInjective` through the spanning
`span_stateOpenCoeff_eq_top`).

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The complement row as an in-region endpoint operator

The explicit complement row `regionComplementRow B R f N σ` of the second tensor
(`TNLean.PEPS.RegionBlock.Recovery7`) is, at the complement boundary configuration
`w`, the incident-matrix sum of `N` against the second tensor's region blocked
weights. The inner-sum realization `region_innerSum_eq_realized`
(`TNLean.PEPS.RegionBlock.Recovery2`) reads that sum as the second tensor's *own*
in-region endpoint operator of `N.transpose`, applied to the second tensor's region
weight vector at the reindexed boundary configuration, evaluated at the endpoint
leg. This is the second-tensor counterpart of the v-side row `vSideRow`
(`TNLean.PEPS.RegionBlock.Recovery10`), which reads the *first* tensor's operator on
the same weight vectors; matching the two rows is the coefficient transfer. -/

/-- **The complement row as the second tensor's in-region endpoint operator.** At a
complement boundary configuration `w` of `univ \ R`, the explicit complement row of
the matrix `N` on the second tensor equals the second tensor's in-region endpoint
operator from `N.transpose`, applied to the second tensor's region weight vector at
the reindexed boundary configuration, evaluated at the endpoint physical leg `σ v`.

This is `region_innerSum_eq_realized` (`TNLean.PEPS.RegionBlock.Recovery2`)
specialized to the second tensor with the boundary configuration
`(regionComplementBoundaryConfigEquiv B R).symm w`. It exposes the complement row of
`regionComplementRow` (`TNLean.PEPS.RegionBlock.Recovery7`) in the same form as the
v-side row `vSideRow` (`TNLean.PEPS.RegionBlock.Recovery10`), so the coefficient
transfer becomes the agreement of the two operators on the same weight vectors.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionComplementRow_eq_regionInsertionOp (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (w : RegionBoundaryConfig (G := G) B (Finset.univ \ R)) :
    regionComplementRow (G := G) B R f N σ w =
      regionInsertionOp (G := G) B R f hvB N.transpose
          (regionWeightVec (G := G) B R f
            ((regionComplementBoundaryConfigEquiv (G := G) B R).symm w) σ)
        (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩) := by
  classical
  rw [regionComplementRow]
  exact region_innerSum_eq_realized B R f hvB N
    ((regionComplementBoundaryConfigEquiv (G := G) B R).symm w) σ

/-! ### The coefficient transfer from agreement of the two endpoint operators

The v-side factorization `regionInsertedCoeff_eq_complement_blockedMap_vSideRow`
(`TNLean.PEPS.RegionBlock.Recovery10`) writes the first tensor's region-inserted
coefficient of `M`, as a function of the complement physical configuration, as the
second tensor's complement blocked tensor map of the v-side row `vSideRow`. The
B-side factorization `regionInsertedCoeff_eq_complement_blockedMap`
(`TNLean.PEPS.RegionBlock.Recovery7`) does the same for the second tensor's
region-inserted coefficient of `N`, with row the explicit complement row
`regionComplementRow B R f N σ`. Both factor through the *same* injective complement
blocked tensor map (`hCB`), so the coefficient transfer is equivalent to matching
the two rows at every region physical configuration. By
`regionComplementRow_eq_regionInsertionOp` and the definition of `vSideRow`, the two
rows agree exactly when the first tensor's in-region endpoint operator (from
`M.transpose`) and the second tensor's (from `N.transpose`) agree on the second
tensor's region weight vectors at the endpoint leg. This is the block-granularity
inversion of the complement away from the in-region endpoint, the region port of
`resonate_invert_right_endpoint`; it uses no single-vertex spanning. -/

/-- **The coefficient transfer from endpoint-operator agreement.** If the first
tensor's in-region endpoint operator from `M.transpose` and the second tensor's from
`N.transpose` agree, at the endpoint physical leg, on the second tensor's region
weight vectors at every reindexed complement boundary configuration and region
physical configuration, then the region-inserted coefficient of `M` in the first
tensor equals that of `N` in the second at every physical configuration.

The two rows of the (shared) injective complement blocked tensor map are the v-side
row `vSideRow A B R f hvA M σ` (the first tensor's operator on the weight vectors)
and the explicit complement row `regionComplementRow B R f N σ` (read by
`regionComplementRow_eq_regionInsertionOp` as the second tensor's operator on the
same weight vectors). The hypothesis matches them, so `hCB` injectivity forces the
coefficients equal through `regionInsertedCoeff_eq_of_complementRow_eq`
(`TNLean.PEPS.RegionBlock.Recovery10`). The argument is region-injective: it inverts
only the second tensor's complement block, never the single vertex `v`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem coeffTransfer_of_endpointOp_eq (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hop : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (ν : RegionBoundaryConfig (G := G) B R),
      regionInsertionOp (G := G) A R f hvA M.transpose
          (regionWeightVec (G := G) B R f ν σ)
          (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
            regionBoundaryEdgeInVertex_mem (G := G) R f⟩) =
        regionInsertionOp (G := G) B R f hvB N.transpose
          (regionWeightVec (G := G) B R f ν σ)
          (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
            regionBoundaryEdgeInVertex_mem (G := G) R f⟩))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ := by
  refine regionInsertedCoeff_eq_of_complementRow_eq A B R f hvA hAB hDim M N (fun σ' => ?_) σ τ
  funext w
  rw [vSideRow, regionComplementRow_eq_regionInsertionOp B R f hvB N σ' w]
  exact hop σ' ((regionComplementBoundaryConfigEquiv (G := G) B R).symm w)

/-! ### The symmetric reduction: coefficient transfer through the region block

The σ-side mirror of `regionInsertedCoeff_eq_of_complementRow_eq`
(`TNLean.PEPS.RegionBlock.Recovery10`). Fixing the complement physical
configuration `τ`, the first tensor's region-inserted coefficient of `M` factors, as
a function of the region physical configuration `σ`, through the second tensor's
region blocked tensor map with row `complSideRow A B R f hvAout M τ`
(`regionInsertedCoeff_eq_region_blockedMap_B`, `Recovery10`); the second tensor's
region-inserted coefficient of `N` factors through the *same* map with the explicit
region row `regionRegionRow B R f N τ` (`regionInsertedCoeff_eq_region_blockedMap`,
`Recovery7`). Region-block injectivity (`hRB`) forces the coefficients equal when the
two rows agree. This is the σ-side inversion, the region port of
`resonate_invert_left_endpoint`. -/

/-- **Coefficient transfer through the region block.** If the σ-side row
`complSideRow A B R f hvAout M τ` of the first tensor agrees with the explicit region
row `regionRegionRow B R f N τ` of the second tensor at every complement physical
configuration `τ`, then the region-inserted coefficient of `M` in the first tensor
equals that of `N` in the second at every physical configuration.

Both rows are rows of the same injective region blocked tensor map of `B` (`hRB`):
the first tensor's coefficient is its map of `complSideRow` by
`regionInsertedCoeff_eq_region_blockedMap_B` (`Recovery10`), the second tensor's of
`regionRegionRow` by `regionInsertedCoeff_eq_region_blockedMap` (`Recovery7`). This
is the σ-side mirror of `regionInsertedCoeff_eq_of_complementRow_eq`; it inverts only
the second tensor's region block.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_of_regionRow_eq (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hrow : ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
      complSideRow (G := G) A B R f hvAout M τ = regionRegionRow (G := G) B R f N τ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ := by
  have hA := congrFun
    (regionInsertedCoeff_eq_region_blockedMap_B A B R f hvAout hAB hDim M τ) σ
  rw [hA, hrow τ, ← regionInsertedCoeff_eq_region_blockedMap B R f N σ τ]

end PEPS
end TNLean
