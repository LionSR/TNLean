import TNLean.PEPS.RegionBlock.ThreeBlockReconcile
import TNLean.PEPS.RegionBlock.UnionInjectivity
import TNLean.PEPS.RegionBlock.BlockCoeffTransfer

/-!
# The block-frame coefficient transfer and per-edge gauge for the normal PEPS theorem

This file wires the three-block engine (`TNLean.PEPS.RegionBlock.ThreeBlockReconcile`),
the union injectivity of the host block (`TNLean.PEPS.RegionBlock.UnionInjectivity`),
and the two-block backbone (`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) into the
per-edge gauge of `TNLean.PEPS.RegionBlock.RegionReconcile`, for two tensors blocked
around the same edge into the same red/blue/complement triple.

The union lemma `regionBlockedTensorInjective_compl_red`
(`TNLean.PEPS.RegionBlock.UnionInjectivity`) supplies the host-block injectivity
`RegionBlockedTensorInjective A (univ \ red)` that every backbone lemma of
`TNLean.PEPS.RegionBlock.BlockCoeffTransfer` needs at the complement of the red
region. With it, the two block-injectivity hypotheses of both tensors at `red` and
at `univ \ red` are all available from the one-edge blocking data and positive bond
dimensions.

## The packaging

A `SharedNormalEdgeBlockingData` records a one-edge blocking datum for each of two
tensors `A`, `B` around the same edge, sharing the same red, blue, and complement
regions. From it the four block-injectivity facts the backbone consumes —
`RegionBlockedTensorInjective A red`, `RegionBlockedTensorInjective A (univ \ red)`,
and the same for `B` — are read off directly: the region injectivities are the
blocking-data fields, and the host-block injectivities are the union lemma.

## The reduction to bond locality

By the block-frame reconcile-is-transfer bridge
`transferCoeff_eq_incidentKernel_iff_coeff_eq`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`), the coefficient transfer
`∀ M, ∃ N, ∀ σ τ, coeff_A M = coeff_B N` (the input `htransferAB` of the per-edge
gauge) holds exactly when, for every inserted matrix `M`, the transfer kernel
`transferCoeff A B red f M` is the incident-matrix kernel of some bond matrix `N` on
the boundary edge `f`. The latter is the **bond locality** of the transfer kernel:
the kernel couples the two boundary configurations only through their legs on `f`.
This is the block-level content of the source step `V=W`. The single remaining open
fact is therefore packaged here as the predicate `IsBondLocalTransferKernel`, and the
per-edge gauge is assembled unconditionally on top of it.

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

/-! ### Shared one-edge blocking data for two tensors

The faithful two-tensor packaging of the source comparison: the two tensors `A` and
`B` are blocked around the **same** edge into the **same** red, blue, and complement
regions, with each region injective for each tensor. A single
`NormalEdgeBlockingData` carries the regions and one tensor's injectivity; the
shared datum adds the second tensor's blocking datum with equal regions. -/

/-- **Shared one-edge blocking data.** A one-edge blocking datum for the first tensor
`A` and one for the second tensor `B`, both around the edge `e`, sharing the same
red, blue, and complement regions.

The source comparison blocks both tensors of `SameState A B` around the same edge
into the same three injective regions (arXiv:1804.04964, Section 3, proof of
Theorem 3). The shared regions are the content of the equalities `red_eq`, `blue_eq`,
`complement_eq`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
structure SharedNormalEdgeBlockingData (A B : Tensor G d) (e : Edge G) where
  /-- The first tensor's one-edge blocking datum. -/
  dataA : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e
  /-- The second tensor's one-edge blocking datum. -/
  dataB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e
  /-- The two tensors share the red region. -/
  red_eq : dataB.red = dataA.red
  /-- The two tensors share the blue region. -/
  blue_eq : dataB.blue = dataA.blue
  /-- The two tensors share the complement region. -/
  complement_eq : dataB.complement = dataA.complement

namespace SharedNormalEdgeBlockingData

variable {A B : Tensor G d} {e : Edge G}

/-- The shared red region. -/
def red (D : SharedNormalEdgeBlockingData A B e) : Finset V := D.dataA.red

/-- The shared blue region. -/
def blue (D : SharedNormalEdgeBlockingData A B e) : Finset V := D.dataA.blue

/-- The shared complement region. -/
def complement (D : SharedNormalEdgeBlockingData A B e) : Finset V := D.dataA.complement

end SharedNormalEdgeBlockingData

end PEPS
end TNLean
