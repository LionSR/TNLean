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

/-! ### The v-side row through the virtual pullback

The v-side row is the first tensor's in-region endpoint operator
`regionInsertionOp A R f hvA M.transpose`, applied to the *second* tensor's region
weight vector at the reindexed complement boundary configuration, read at the
endpoint leg. The region weight vector is the second tensor's local tensor map of
the region open coefficient, so the unconditional image-preservation realization
`localTensorMap_localVirtualOpOfPhysicalOpAt_regionInsertionOp` (`Recovery4`)
rewrites the endpoint operator's action as the second tensor's local tensor map of
the virtual pullback `W` applied to the region open coefficient. This is the region
analogue of inverting an endpoint of the resonate identity: the action of the
first tensor's operator on the second tensor's weight vectors runs entirely through
the virtual pullback `W`. -/

/-- **The v-side row through the virtual pullback.** The v-side row equals the
second tensor's local tensor map of the virtual pullback
`W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose)`
applied to the second tensor's region open coefficient at the reindexed complement
boundary configuration, read at the endpoint leg.

The region weight vector is the second tensor's local tensor map of the region open
coefficient (by definition of `regionWeightVec`), and the unconditional
image-preservation realization
`localTensorMap_localVirtualOpOfPhysicalOpAt_regionInsertionOp` rewrites the first
tensor's endpoint operator on a second-tensor local tensor image as the second
tensor's local tensor map of the virtual pullback. This holds with no matrix
read-off, so it is non-circular.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem vSideRow_eq_localTensorMap_virtualPullback (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)) :
    vSideRow (G := G) A B R f hvA M σ ν' =
      localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
          (localVirtualOpOfPhysicalOpAt B hvB
            (regionInsertionOp (G := G) A R f hvA M.transpose)
            (regionOpenCoeff (G := G) B R f
              ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') σ))
        (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩) := by
  rw [vSideRow, regionWeightVec,
    ← localTensorMap_localVirtualOpOfPhysicalOpAt_regionInsertionOp A B R f hvA hvB hAB hA hB
      hposA hposB M
      (regionOpenCoeff (G := G) B R f
        ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') σ)]

/-! ### The incident-matrix form of the v-side row

When the virtual pullback `W` is of incident-matrix form on the boundary leg —
`W = localIncidentMatrixOp B inc N.transpose` for a matrix `N` on the second
tensor's bond — the v-side row collapses to the incident-matrix coupling of `N`
against the second tensor's region blocked weights. The local tensor map of the
incident insertion is the second tensor's own in-region endpoint operator of
`N.transpose` (by `regionInsertionOp_realizes`), and reading it at the endpoint leg
is the inner-sum realization `region_innerSum_eq_realized`, the explicit
incident-matrix sum. This is the v-side half of the region reconcile. -/

open scoped Classical in
/-- **The incident-matrix form of the v-side row.** If the virtual pullback
`W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose)`
is of incident-matrix form `localIncidentMatrixOp B inc N.transpose`, then the
v-side row at the complement boundary configuration `ν'` is the incident-matrix
coupling of `N` on the boundary edge against the second tensor's region blocked
weights, with the residual legs contracted by the identity:
`vSideRow … σ ν' = ∑_μ (if SameAwayFromBond f μ ((E B R).symm ν') then N (μ f)
(((E B R).symm ν') f) else 0) · WB_R(μ, σ)`.

The v-side row is the second tensor's local tensor map of `W` applied to the region
open coefficient (`vSideRow_eq_localTensorMap_virtualPullback`); substituting the
incident-matrix form of `W` and applying `regionInsertionOp_realizes` rewrites it as
the second tensor's in-region endpoint operator of `N.transpose` on the region
weight vector, which the inner-sum realization `region_innerSum_eq_realized`
expands to the incident-matrix sum.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem vSideRow_eq_incidentSum_of_virtualPullback_incidentForm (A B : Tensor G d)
    (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hform : localVirtualOpOfPhysicalOpAt B hvB
        (regionInsertionOp (G := G) A R f hvA M.transpose) =
      localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)) :
    vSideRow (G := G) A B R f hvA M σ ν' =
      ∑ μ : RegionBoundaryConfig (G := G) B R,
        (if SameAwayFromBond f μ
              ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') then
            N (μ f) (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f) else 0) *
          regionBlockedWeight (G := G) B R μ σ := by
  classical
  rw [vSideRow_eq_localTensorMap_virtualPullback A B R f hvA hvB hAB hA hB hposA hposB M σ ν',
    hform,
    ← regionInsertionOp_realizes B R f hvB N.transpose
      (regionOpenCoeff (G := G) B R f
        ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') σ),
    ← regionWeightVec,
    ← region_innerSum_eq_realized B R f hvB N
      ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') σ]

/-! ### The incident-matrix form of the transfer coefficient from the virtual pullback

Combining the region read-off of the transfer-coefficient column with the
incident-matrix form of the v-side row gives the incident-matrix form of the
transfer coefficient itself: when the virtual pullback `W` is of incident-matrix
form `localIncidentMatrixOp B inc N.transpose`, the transfer coefficient is the
incident-matrix coupling of `N` on the boundary edge `f`, with the residual legs
contracted by the identity. This is the `hform` hypothesis of
`regionInsertedCoeff_eq_of_transferCoeff_form` (`Recovery10`), reduced to the
incident-matrix structure of the virtual pullback. -/

open scoped Classical in
/-- **The incident-matrix form of the transfer coefficient.** If the virtual pullback
`W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose)`
is of incident-matrix form `localIncidentMatrixOp B inc N.transpose` for a matrix
`N` on the second tensor's bond, then the transfer coefficient has the
incident-matrix coupling form of `N` on the boundary edge `f`:
`transferCoeff … μ ν' = if SameAwayFromBond f μ ((E B R).symm ν') then N (μ f)
(((E B R).symm ν') f) else 0`.

The transfer-coefficient column is the second tensor's region blocked left inverse of
the v-side row (`transferCoeff_column_eq_regionBlockedLeftInverse_vSideRow`); the
v-side row is the incident-matrix sum of `N` against the region blocked weights
(`vSideRow_eq_incidentSum_of_virtualPullback_incidentForm`), so the left inverse
collapses each blocked weight to the standard basis configuration
(`regionBlockedLeftInverse_regionBlockedWeight`), reading off the incident-matrix
coupling at the configuration `μ`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem transferCoeff_eq_incidentForm_of_virtualPullback_incidentForm (A B : Tensor G d)
    (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hform : localVirtualOpOfPhysicalOpAt B hvB
        (regionInsertionOp (G := G) A R f hvA M.transpose) =
      localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose)
    (μ : RegionBoundaryConfig (G := G) B R)
    (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)) :
    transferCoeff (G := G) A B R hRB hCB f M μ ν' =
      (if SameAwayFromBond f μ
            ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') then
          N (μ f) (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f) else 0) := by
  classical
  have hcol := congrFun
    (transferCoeff_column_eq_regionBlockedLeftInverse_vSideRow
      A B R hRB hCB f hvA hvAout hAB hDim M ν') μ
  rw [hcol]
  -- The v-side row is the incident-matrix sum, i.e. the region blocked tensor map of
  -- the incident-matrix coupling column; the region left inverse collapses it.
  have hvrow : (fun σ : RegionPhysicalConfig (V := V) (d := d) R =>
        vSideRow (G := G) A B R f hvA M σ ν') =
      regionBlockedTensorMap (G := G) B R
        (fun μ' : RegionBoundaryConfig (G := G) B R =>
          (if SameAwayFromBond f μ'
                ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') then
              N (μ' f) (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f)
            else 0)) := by
    funext σ
    rw [vSideRow_eq_incidentSum_of_virtualPullback_incidentForm
      A B R f hvA hvB hAB hA hB hposA hposB M N hform σ ν', regionBlockedTensorMap_apply]
    refine Finset.sum_congr rfl (fun μ' _ => ?_)
    rw [smul_eq_mul]
  rw [hvrow, regionBlockedLeftInverse_apply_regionBlockedTensorMap]

end PEPS
end TNLean
