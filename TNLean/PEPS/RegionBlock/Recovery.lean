import TNLean.PEPS.RegionBlock.Algebra
import TNLean.PEPS.NormalFundamentalTheorem

/-!
# Region realization and the region insertion transfer

This file builds the region analogue of the physical-to-virtual recovery
`physical_to_virtual_insertion`, supplying the data of a `RegionInsertionTransfer`
on a boundary edge of an arbitrary finite region `R`.

The edge-level recovery of `TNLean.PEPS.InsertionAlgebra` realizes a matrix
insertion on the chosen bond as a physical operator at one endpoint vertex,
transfers it to the second tensor across `SameState`, and reads the matrix back
off. The region analogue realizes the matrix insertion at the single in-region
endpoint vertex of the boundary edge `f`, which is the one endpoint of `f` lying
in `R`.

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

/-! ### The in-region endpoint of a boundary edge

A boundary edge `f` of `R` has exactly one endpoint in `R`. That endpoint is the
in-region endpoint; the matrix insertion on `f` is realized as a physical
operator at this vertex. -/

end PEPS
end TNLean
