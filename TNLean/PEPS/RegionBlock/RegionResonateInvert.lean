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

end PEPS
end TNLean
