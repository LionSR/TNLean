import TNLean.PEPS.RegionBlock.RegionReconcile
import TNLean.PEPS.InsertionRealization

/-!
# Region resonate inversion: the bond-contracted endpoint-inversion engine

This file ports the resonate inversion of the edge-blocked physical-to-virtual
recovery (`TNLean.PEPS.InsertionRealization`) to **region granularity**, in the
region-injective regime. The edge engine inverts the middle block of an
edge-centered three-site chain (`resonate_middle_inverted`) and the two endpoint
vertices (`resonate_invert_right_endpoint`, `resonate_invert_left_endpoint`) to
read a matrix off the resonate identity. The region engine inverts the
complement block of `R` (resp. the region block) through the blocked-region left
inverses `regionBlockedLeftInverse B (univ \ R) hCB` / `regionBlockedLeftInverse
B R hRB` (the residual analogue of the edge middle), and the two endpoint
vertices through `localLeftInverseAt B hvB` / `localLeftInverseAt B hvBout`.

The boundary edge `f` connects the in-region endpoint
`regionBoundaryEdgeInVertex R f` and the out-of-region endpoint
`regionBoundaryEdgeOutVertex R f`; the interior of the region/complement split is
empty, so the two endpoint blocks are exactly the region block and the complement
block. The resonate identity input is `region_resonate_identity`
(`TNLean.PEPS.RegionBlock.Recovery7`), the region analogue of the edge resonate
identity that `physical_to_virtual_insertion` consumes.

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

/-! ### The doubly-blocked resonate identity

The region analogue of the edge resonate identity `hEq` that
`physical_to_virtual_insertion` (`TNLean.PEPS.InsertionRealization`) consumes. The
first tensor's region-inserted coefficient of `M` factors through the second
tensor's *complement* block (with row the v-side row `vSideRow`,
`regionInsertedCoeff_eq_complement_blockedMap_vSideRow`) and, equally, through the
second tensor's *region* block (with row the σ-side row `complSideRow`,
`regionInsertedCoeff_eq_region_blockedMap_B`). Equating the two readings gives the
doubly-blocked resonate identity: the second tensor's complement blocked tensor map
of the v-side row equals its region blocked tensor map of the σ-side row, for every
physical configuration.

This identity reads the two tensors only through the `SameState`-invariant
region-inserted coefficient and uses no single-vertex injectivity. The two endpoint
blocks of `B` it equates are exactly the region and complement blocks; inverting
them (through the blocked-region left inverses) is the residual analogue of stripping
the edge middle, and is the starting point of the region resonate inversion. -/

/-- **The doubly-blocked resonate identity.** The second tensor's complement blocked
tensor map of the v-side row of `M`, evaluated at the complement physical
configuration `τ`, equals the second tensor's region blocked tensor map of the σ-side
row of `M`, evaluated at the region physical configuration `σ`.

Both sides equal the first tensor's region-inserted coefficient of `M`: the left side
by the v-side factorization
`regionInsertedCoeff_eq_complement_blockedMap_vSideRow`, the right side by the σ-side
factorization `regionInsertedCoeff_eq_region_blockedMap_B`. It is the region analogue
of the edge resonate identity, expressed through the second tensor's two endpoint
blocks, and uses no single-vertex injectivity.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem doubleBlockedResonate (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionBlockedTensorMap (G := G) B (Finset.univ \ R)
        (vSideRow (G := G) A B R f hvA M σ) τ =
      regionBlockedTensorMap (G := G) B R
        (complSideRow (G := G) A B R f hvAout M τ) σ := by
  have hv := congrFun
    (regionInsertedCoeff_eq_complement_blockedMap_vSideRow A B R f hvA hAB hDim M σ) τ
  have hσ := congrFun
    (regionInsertedCoeff_eq_region_blockedMap_B A B R f hvAout hAB hDim M τ) σ
  rw [← hv, hσ]

/-! ### The symmetric block read-off of the transfer coefficient

The doubly-inverted transfer coefficient `transferCoeff` is read off the first
tensor's region-inserted coefficient by inverting the second tensor's region block
and then its complement block (`vSideRow_eq_region_blockedMap_transferCoeff`,
`TNLean.PEPS.RegionBlock.Recovery10`). The other order — invert the complement block
first, through the σ-side row `complSideRow`, then the region block — reads off the
same transfer coefficient. This is the region analogue of the V=W reconcile
`resonate_endpoint_coeff_reconcile` (`TNLean.PEPS.InsertionRealization`): the matrix
read off by inverting one endpoint equals that read off by inverting the other. Both
orders use only the blocked-region left inverses; neither uses single-vertex
injectivity. -/

/-- **The σ-side row through the transfer coefficient.** The σ-side row at the region
boundary configuration `μ`, as a function of the complement physical configuration, is
the second tensor's complement blocked tensor map applied to the transfer-coefficient
row `fun ν' => transferCoeff … μ ν'`.

The σ-side row equals the region row `regionRowB` (`regionRowB_eq_complSideRow`,
`Recovery10`); the region row, as a function of the complement physical configuration,
is the second tensor's complement blocked tensor map of the transfer coefficient
(`regionRowB_eq_complement_blockedMap`, `Recovery10`). This is the complement-first
read-off, mirroring `vSideRow_eq_region_blockedMap_transferCoeff`, and uses no
single-vertex injectivity.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem complSideRow_eq_complement_blockedMap_transferCoeff (A B : Tensor G d)
    (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (μ : RegionBoundaryConfig (G := G) B R) :
    (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        complSideRow (G := G) A B R f hvAout M τ μ) =
      regionBlockedTensorMap (G := G) B (Finset.univ \ R)
        (transferCoeff (G := G) A B R hRB hCB f M μ) := by
  rw [← regionRowB_eq_complement_blockedMap A B R hRB hCB f hvA hAB hDim M μ]
  funext τ
  rw [regionRowB_eq_complSideRow A B R hRB f hvAout hAB hDim M τ]

/-! ### The incident-matrix form of the transfer coefficient from the v-side row

The remaining endpoint inversion of the region resonate step is the read-off of a
single bond matrix `N` from the v-side row: the v-side row of `M` is the
incident-matrix coupling of `N` on the boundary edge `f` against the second tensor's
region blocked weights. Given that read-off (the hypothesis `hvrow` below, the region
analogue of the conclusion of `resonate_invert_right_endpoint`), the transfer
coefficient inherits the incident-matrix coupling form, region-injectively: the
transfer-coefficient column is the region blocked left inverse of the v-side row
(`transferCoeff_column_eq_regionBlockedLeftInverse_vSideRow`), and the left inverse
collapses each blocked weight to its standard basis configuration
(`regionBlockedLeftInverse_regionBlockedWeight`), reading off the coupling at `μ`.

This is the region-injective replacement for
`transferCoeff_eq_incidentForm_of_virtualPullback_incidentForm`
(`TNLean.PEPS.RegionBlock.Recovery11`), which derives the incident form from the
virtual pullback and so threads single-vertex injectivity through the
image-preservation realization. The hypothesis here is the v-side-row incident form
itself, the genuine output of the endpoint-vertex inversion. -/

open scoped Classical in
/-- **The incident-matrix form of the transfer coefficient from the v-side row.** If
the v-side row of `M` is, at every region physical configuration `σ`, the
incident-matrix coupling of a bond matrix `N` on `f` against the second tensor's
region blocked weights (with the residual legs contracted by the identity), then the
transfer coefficient has the incident-matrix coupling form of `N` on `f`.

The transfer-coefficient column is the region blocked left inverse of the v-side row
(`transferCoeff_column_eq_regionBlockedLeftInverse_vSideRow`, `Recovery11`); the
hypothesis writes the v-side row as the region blocked tensor map of the
incident-matrix coupling column, so the left inverse recovers the column
(`regionBlockedLeftInverse_apply_regionBlockedTensorMap`). This uses only the
blocked-region left inverses, no single-vertex injectivity, replacing
`transferCoeff_eq_incidentForm_of_virtualPullback_incidentForm` (`Recovery11`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem transferCoeff_eq_incidentForm_of_vSideRow_incidentForm (A B : Tensor G d)
    (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hvrow : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)),
      vSideRow (G := G) A B R f hvA M σ ν' =
        ∑ μ : RegionBoundaryConfig (G := G) B R,
          (if SameAwayFromBond f μ
                ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') then
              N (μ f) (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f) else 0) *
            regionBlockedWeight (G := G) B R μ σ)
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
  -- The v-side row is the region blocked tensor map of the incident-matrix coupling column.
  have hmap : (fun σ : RegionPhysicalConfig (V := V) (d := d) R =>
        vSideRow (G := G) A B R f hvA M σ ν') =
      regionBlockedTensorMap (G := G) B R
        (fun μ' : RegionBoundaryConfig (G := G) B R =>
          (if SameAwayFromBond f μ'
                ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') then
              N (μ' f) (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f)
            else 0)) := by
    funext σ
    rw [hvrow σ ν', regionBlockedTensorMap_apply]
    refine Finset.sum_congr rfl (fun μ' _ => ?_)
    rw [smul_eq_mul]
  rw [hmap, regionBlockedLeftInverse_apply_regionBlockedTensorMap]

/-! ### The coefficient transfer from the v-side-row incident form

Composing the incident-matrix form of the transfer coefficient
(`transferCoeff_eq_incidentForm_of_vSideRow_incidentForm`) with the double
factorization bridge `regionInsertedCoeff_eq_of_transferCoeff_form`
(`TNLean.PEPS.RegionBlock.Recovery10`) closes the coefficient transfer
region-injectively: the first tensor's region-inserted coefficient of `M` equals the
second tensor's of `N` at every physical configuration. The only input is the
v-side-row incident form, the output of the endpoint-vertex inversion; no
single-vertex injectivity is used. -/

open scoped Classical in
/-- **The coefficient transfer from the v-side-row incident form.** If the v-side row
of `M` is the incident-matrix coupling of a bond matrix `N` on `f` against the second
tensor's region blocked weights at every region physical configuration, then the first
tensor's region-inserted coefficient of `M` equals the second tensor's of `N` at every
physical configuration.

The transfer coefficient has the incident-matrix coupling form of `N`
(`transferCoeff_eq_incidentForm_of_vSideRow_incidentForm`); the double factorization
bridge `regionInsertedCoeff_eq_of_transferCoeff_form` then matches the coefficients.
This is region-injective: it inverts only the second tensor's blocks, never the single
endpoint vertex.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_of_vSideRow_incidentForm (A B : Tensor G d)
    (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hvrow : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)),
      vSideRow (G := G) A B R f hvA M σ ν' =
        ∑ μ : RegionBoundaryConfig (G := G) B R,
          (if SameAwayFromBond f μ
                ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') then
              N (μ f) (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f) else 0) *
            regionBlockedWeight (G := G) B R μ σ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ :=
  regionInsertedCoeff_eq_of_transferCoeff_form A B R hRB hCB f hvA hvAout hAB hDim M N
    (fun μ ν' => transferCoeff_eq_incidentForm_of_vSideRow_incidentForm
      A B R hRB hCB f hvA hvAout hAB hDim M N hvrow μ ν') σ τ

end PEPS
end TNLean
