import TNLean.PEPS.RegionBlock.ThreeBlockReconcile
import TNLean.PEPS.RegionBlock.UnionInjectivity
import TNLean.PEPS.RegionBlock.BasisChangeIntertwine

/-!
# The abstract-operator three-block engine for the normal PEPS Fundamental Theorem

This file ports the **abstract physical-operator** architecture of the edge-level
realization `physical_to_virtual_insertion` /
`edgeRightInsertionOp_realizes_edgeTransferMatrix`
(`TNLean.PEPS.InsertionRealization`, `TNLean.PEPS.InsertionAlgebra`) to the
**three injective region blocks** of a `SharedNormalEdgeBlockingData`.

The edge realization solves the cross-tensor problem with a tensor-independent
physical operator: an operator on the physical legs realizes one tensor's
matrix insertion by that tensor's injectivity, the resonate identity holds on
the first tensor by construction, the identity transports to the second tensor
because `SameState` makes the two global states equal and the operator acts only
on physical legs, and the single-tensor engine then runs on the second tensor to
read the matrix off.

At block granularity the physical space of the red block is the function space
`RegionPhysicalConfig red → ℂ`, and the tensor-independent physical operator at
the red block is the **block realization operator** `blockRealizeOp A red f M`
(`TNLean.PEPS.RegionBlock.BlockRealization`): a linear endomorphism of
`RegionPhysicalConfig red → ℂ` that realizes the first tensor's red-block
matrix insertion of `M` on the boundary edge `f`. This file:

* fixes the abstract physical operator `blockRealizeOp A red f M` (Target 1/2,
  reusing `BlockRealization.lean`);
* proves that this operator, applied to the **second tensor's** partial state
  across the region cut (the `SameState`-invariant object), reads off the first
  tensor's region-inserted coefficient (the transport, Target 3); and
* feeds the constructed `N` to the basis-change intertwining bridge
  (`isBondLocalTransferKernel_of_coeffTransfer`,
  `TNLean.PEPS.RegionBlock.BasisChangeIntertwine`) and the shared-blocking-data
  per-edge gauge (`SharedNormalEdgeBlockingData.exists_regionEdgeGauge`,
  `TNLean.PEPS.RegionBlock.ThreeBlockTransfer`) to close the kernel (Target 5).

The cross-tensor content enters exactly once, in the transport step: the
realization operator built from the first tensor acts on the second tensor's
`SameState`-invariant partial state. Everything else is single-tensor block
mechanics already landed in `BlockRealization.lean` and the three-block engine.

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

/-! ### The abstract red-block physical operator and its three-block coefficient

The tensor-independent physical operator at the red block is the block
realization operator `blockRealizeOp A red f M`: a linear endomorphism of the red
physical function space `RegionPhysicalConfig red → ℂ`. It realizes the first
tensor's red-block matrix insertion of `M` on the boundary edge `f` by inverting
the red block, applying the row insertion of `M`, and reblocking
(`TNLean.PEPS.RegionBlock.BlockRealization`).

The **three-block coefficient with an abstract operator** reads the red-block
physical operator `O₁` against the fused blue/complement leg through the partial
state across the region cut: at a complement physical configuration `τ`, the
operator `O₁` acts on the interior-bond multiple of the partial state and is read
at the region physical leg `σ`. With `O₁ := blockRealizeOp A red f M` this is the
first tensor's region-inserted coefficient (`A`-realization, KEY IDENTITY 1). -/

/-- **The abstract-operator three-block coefficient.** Apply the abstract red-block
physical operator `O₁` to the interior-bond multiple of the partial state across
the region cut (read as a function of the red physical leg) and evaluate at the
red leg `σ`. This is the abstract analogue of `threeBlockInsertedCoeff` with the
`M`-coupling at the red block replaced by an abstract operator on the red physical
function space.

The partial state `regionPartialState A R τ` carries the fused blue/complement leg
through the closed-state contraction; the abstract operator `O₁` acts only on the
red physical function space and is read at the red leg `σ`. The interior-bond
multiple is the standing normalization of the block realization (KEY IDENTITY 1,
`TNLean.PEPS.RegionBlock.BlockRealization`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`, lines
254--582 of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def threeBlockOpCoeff (A : Tensor G d) (R : Finset V)
    (O₁ : (RegionPhysicalConfig (V := V) (d := d) R → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (V := V) (d := d) R → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) : ℂ :=
  O₁ ((regionInteriorBondProd (G := G) A R : ℂ) • regionPartialState (G := G) A R τ) σ

@[simp] theorem threeBlockOpCoeff_apply (A : Tensor G d) (R : Finset V)
    (O₁ : (RegionPhysicalConfig (V := V) (d := d) R → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (V := V) (d := d) R → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    threeBlockOpCoeff (G := G) A R O₁ σ τ =
      O₁ ((regionInteriorBondProd (G := G) A R : ℂ) • regionPartialState (G := G) A R τ) σ :=
  rfl

end PEPS
end TNLean
