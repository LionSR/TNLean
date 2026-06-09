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

end PEPS
end TNLean
