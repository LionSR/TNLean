import TNLean.PEPS.RegionBlock.Recovery10

/-!
# Region physical-to-virtual recovery: the incident-matrix form of the transfer coefficient

This file closes the final reconcile of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3): the **incident-matrix form** of the transfer
coefficient `transferCoeff` (`TNLean.PEPS.RegionBlock.Recovery10`). This is the
region analogue of the source step `V=W` in Lemma `inj_isomorph`, forced by the
region resonate identity together with full injectivity of both blocked
endpoints.

Feeding the form to `regionInsertedCoeff_eq_of_transferCoeff_form`
(`Recovery10`) yields, for each inserted matrix `M`, a matching matrix `N` whose
region-inserted coefficient equals the first tensor's, which is the coefficient
transfer hypothesis of `regionResonateReconcile_of_coeff_transfer`
(`TNLean.PEPS.RegionBlock.Recovery9`), giving the region resonate reconcile
`RegionResonateReconcile` and hence the per-edge gauge
`exists_regionEdgeGauge_of_reconcile` (`TNLean.PEPS.RegionBlock.Recovery8`).

## Strategy

The transfer coefficient column `fun μ => transferCoeff … μ ν'` is the second
tensor's region blocked left inverse of the v-side row
`fun σ => vSideRow … σ ν'` (read off `vSideRow_eq_region_blockedMap_transferCoeff`,
`Recovery10`). The v-side row is the first tensor's in-region endpoint operator,
from `M.transpose`, applied to the *second* tensor's region weight vector at the
reindexed complement boundary configuration. The region resonate inversion (the
analogue of `resonate_invert_right_endpoint`,
`TNLean.PEPS.InsertionRealization`) expresses this endpoint read-off as the
incident-matrix coupling of a single matrix on the boundary bond against the
second tensor's region blocked weights, with the residual legs contracted by the
identity. The region blocked left inverse then collapses to the standard basis,
exhibiting the incident-matrix form of the transfer coefficient.

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

/-! ### The transfer-coefficient column as the region read-off of the v-side row

The transfer coefficient `transferCoeff … μ ν'`, viewed as a column over the
region boundary configuration `μ` at a fixed complement boundary configuration
`ν'`, is the second tensor's region blocked left inverse of the v-side row
`fun σ => vSideRow … σ ν'`. This inverts the region factorization
`vSideRow_eq_region_blockedMap_transferCoeff` (`Recovery10`) and is the read-off
the incident-matrix form is concluded against. -/

/-- **The transfer-coefficient column is the region read-off of the v-side row.**
The transfer coefficient column at the complement boundary configuration `ν'`,
viewed as a function of the region boundary configuration, is the second tensor's
region blocked left inverse applied to the v-side row at `ν'`.

The v-side factorization `vSideRow_eq_region_blockedMap_transferCoeff` writes the
v-side row as the second tensor's region blocked tensor map of the transfer
coefficient column; the region blocked left inverse recovers the column.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem transferCoeff_column_eq_regionBlockedLeftInverse_vSideRow
    (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)) :
    (fun μ => transferCoeff (G := G) A B R hRB hCB f M μ ν') =
      regionBlockedLeftInverse (G := G) B R hRB
        (fun σ => vSideRow (G := G) A B R f hvA M σ ν') := by
  rw [vSideRow_eq_region_blockedMap_transferCoeff A B R hRB hCB f hvA hvAout hAB hDim M ν',
    regionBlockedLeftInverse_apply_regionBlockedTensorMap]

end PEPS
end TNLean
