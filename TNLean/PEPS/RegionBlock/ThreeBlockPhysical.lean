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

/-! ### Target 2: the A-realization

With the abstract red-block operator instantiated as the first tensor's own block
realization operator `blockRealizeOp A red f M`, the abstract-operator three-block
coefficient is the first tensor's region-inserted coefficient of `M`. This is KEY
IDENTITY 1 (`blockRealizeOp_regionPartialState_eq_regionInsertedCoeff`,
`TNLean.PEPS.RegionBlock.BlockRealization`): the realization operator applied to
the interior-bond multiple of the first tensor's partial state recovers the
M-inserted coefficient. -/

/-- **Target 2: the A-realization.** The abstract-operator three-block coefficient
of the first tensor's block realization operator `blockRealizeOp A R hRA f M` is
the first tensor's region-inserted coefficient of `M`. This realizes the abstract
red-block operator as the first tensor's matrix insertion, by KEY IDENTITY 1.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockOpCoeff_blockRealizeOp_eq_regionInsertedCoeff (A : Tensor G d)
    (R : Finset V) (hRA : RegionBlockedTensorInjective (G := G) A R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    threeBlockOpCoeff (G := G) A R (blockRealizeOp (G := G) A R hRA f M) σ τ =
      regionInsertedCoeff (G := G) A R f M σ τ := by
  rw [threeBlockOpCoeff_apply,
    blockRealizeOp_regionPartialState_eq_regionInsertedCoeff (G := G) A R hRA f M τ]

/-! ### Target 3: the resonate transport across `SameState`

The abstract-operator three-block coefficient reads the tensor **only** through
the partial state across the region cut and the interior bond product. The partial
state is `SameState`-invariant (`regionPartialState_sameState`), and the interior
bond products of two tensors with matched bond dimensions coincide
(`regionInteriorBondProd_congr`). So the abstract-operator three-block coefficient
of the **first** tensor equals that of the **second** tensor, for the *same*
abstract red-block operator `O₁`. This is the single cross-tensor step: the
abstract operator built from either tensor acts on the common partial state.

The transport is what lets the realization operator built from the first tensor
read the first tensor's coefficient off the *second* tensor's partial state, the
block port of the edge-level `SameState` transport of the resonate identity. -/

/-- **Target 3: the resonate transport.** The abstract-operator three-block
coefficient is `SameState`-invariant: for the same abstract red-block operator
`O₁`, the first tensor's abstract-operator coefficient (read through the first
tensor's partial state and interior bond product) equals the second tensor's (read
through the second tensor's partial state and interior bond product), under
`SameState` and matched bond dimensions.

The partial states coincide across `SameState` (`regionPartialState_sameState`)
and the interior bond products coincide under `hDim` (`regionInteriorBondProd_congr`),
so the operator `O₁` is applied to the *same* vector on both sides.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`, lines
254--582 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockOpCoeff_transport (A B : Tensor G d) (R : Finset V)
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (O₁ : (RegionPhysicalConfig (V := V) (d := d) R → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (V := V) (d := d) R → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    threeBlockOpCoeff (G := G) A R O₁ σ τ = threeBlockOpCoeff (G := G) B R O₁ σ τ := by
  rw [threeBlockOpCoeff_apply, threeBlockOpCoeff_apply,
    regionPartialState_sameState hAB R τ, regionInteriorBondProd_congr A B R hDim]

/-- **The first tensor's coefficient through the second tensor's realization.** The
first tensor's region-inserted coefficient of `M` is the abstract-operator
three-block coefficient of the first tensor's block realization operator read on
the *second* tensor's partial state. This composes the A-realization (Target 2)
with the resonate transport (Target 3): the realization operator built from the
first tensor reads the first tensor's coefficient off the second tensor's
`SameState`-invariant partial state.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_threeBlockOpCoeff_B (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      threeBlockOpCoeff (G := G) B R (blockRealizeOp (G := G) A R hRA f M) σ τ := by
  rw [← threeBlockOpCoeff_blockRealizeOp_eq_regionInsertedCoeff (G := G) A R hRA f M σ τ,
    threeBlockOpCoeff_transport A B R hAB hDim (blockRealizeOp (G := G) A R hRA f M) σ τ]

/-! ### Target 4: the abstract-operator engine reads the matrix off the second tensor

The single-tensor engine on the second tensor: the second tensor's own block
realization operator `blockRealizeOp B R hRB f N` realizes the second tensor's
region-inserted coefficient of `N` through the second tensor's partial state, by
KEY IDENTITY 1 instanced at the second tensor.

Combining the A-realization-through-B (`regionInsertedCoeff_eq_threeBlockOpCoeff_B`,
the abstract operator built from `A` read on `B`'s partial state) with the B-engine,
the coefficient transfer `coeff_A M = coeff_B N` is exactly the agreement of the two
block realization operators — the one built from `A` with matrix `M`, the one built
from `B` with matrix `N` — on the interior-bond multiple of the second tensor's
partial state. This is the block port of the edge engine's reading of the matrix off
the second tensor: the cross-tensor operator is realized as a second-tensor matrix
insertion on the second tensor's `SameState`-invariant column. -/

/-- **Target 4: the second tensor's block realization on its own partial state.** The
abstract-operator three-block coefficient of the second tensor's block realization
operator `blockRealizeOp B R hRB f N`, read on the second tensor's data, is the
second tensor's region-inserted coefficient of `N`. This is Target 2 instanced at
the second tensor: the engine on `B`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockOpCoeff_B_blockRealizeOp_eq_regionInsertedCoeff (B : Tensor G d)
    (R : Finset V) (hRB : RegionBlockedTensorInjective (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    threeBlockOpCoeff (G := G) B R (blockRealizeOp (G := G) B R hRB f N) σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ :=
  threeBlockOpCoeff_blockRealizeOp_eq_regionInsertedCoeff (G := G) B R hRB f N σ τ

/-- **The coefficient transfer is the agreement of the two block realization
operators on the second tensor's partial state.** For a witness matrix `N`, the
first tensor's region-inserted coefficient of `M` equals the second tensor's of `N`
at every physical configuration if and only if the two block realization operators —
the one built from `A` with matrix `M`, the one built from `B` with matrix `N` —
agree on the interior-bond multiple of the second tensor's partial state across the
region cut, at every complement physical configuration.

The forward direction reads each coefficient through the corresponding block
realization (the A-realization through `B`, Target 3; the B-realization, Target 4);
the backward direction inverts the same readings. This is the block port of the edge
engine's matrix read-off: the cross-tensor operator is realized as a second-tensor
matrix insertion on the second tensor's `SameState`-invariant column.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
254--582 of `Papers/1804.04964/paper_normal.tex`. -/
theorem coeffTransfer_iff_blockRealizeOp_agree (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    (∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f N σ τ) ↔
      (∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
        blockRealizeOp (G := G) A R hRA f M
            ((regionInteriorBondProd (G := G) B R : ℂ) • regionPartialState (G := G) B R τ) =
          blockRealizeOp (G := G) B R hRB f N
            ((regionInteriorBondProd (G := G) B R : ℂ) • regionPartialState (G := G) B R τ)) := by
  constructor
  · intro hcoeff τ
    funext σ
    have hA := regionInsertedCoeff_eq_threeBlockOpCoeff_B A B R hRA hAB hDim f M σ τ
    have hB := threeBlockOpCoeff_B_blockRealizeOp_eq_regionInsertedCoeff B R hRB f N σ τ
    rw [threeBlockOpCoeff_apply] at hA
    rw [threeBlockOpCoeff_apply] at hB
    rw [← hA, hcoeff σ τ, hB]
  · intro hagree σ τ
    have hA := regionInsertedCoeff_eq_threeBlockOpCoeff_B A B R hRA hAB hDim f M σ τ
    have hB := threeBlockOpCoeff_B_blockRealizeOp_eq_regionInsertedCoeff B R hRB f N σ τ
    rw [threeBlockOpCoeff_apply] at hA hB
    rw [hA, congrFun (hagree τ) σ, hB]

/-! ### The abstract-operator V=W predicate

The genuinely cross-tensor content of the per-edge gauge, isolated by the
abstract-operator engine: for every inserted matrix `M` on the first tensor's bond
there is a matrix `N` on the second tensor's bond such that the two block
realization operators — the one built from `A` with `M`, the one built from `B`
with `N` — agree on the second tensor's partial states. By
`coeffTransfer_iff_blockRealizeOp_agree` this operator agreement is exactly the
coefficient transfer `coeff_A M = coeff_B N`, so the predicate is the engine's
form of the block step `V=W`: the cross-tensor red-block operator, read on the
second tensor's `SameState`-invariant column, is a second-tensor matrix insertion. -/

/-- **The abstract-operator V=W predicate.** For every inserted matrix `M` on the
boundary edge `f`, there is a matrix `N` on the second tensor's bond such that the
two block realization operators agree on every interior-bond multiple of the second
tensor's partial state across the region cut.

This is the engine's isolation of the block step `V=W`: the red-block operator built
from the first tensor, read on the second tensor's `SameState`-invariant column, is
realized as a second-tensor matrix insertion. -/
def BlockRealizeOpAgree (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : Prop :=
  ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
    ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
      ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
        blockRealizeOp (G := G) A R hRA f M
            ((regionInteriorBondProd (G := G) B R : ℂ) • regionPartialState (G := G) B R τ) =
          blockRealizeOp (G := G) B R hRB f N
            ((regionInteriorBondProd (G := G) B R : ℂ) • regionPartialState (G := G) B R τ)

/-- **The abstract-operator V=W predicate gives the coefficient transfer.** If the two
block realization operators agree (for some `N` per `M`) on the second tensor's
partial states, then for every inserted matrix `M` there is a matrix `N` whose
region-inserted coefficient matches the first tensor's of `M` at every physical
configuration. This unpacks `BlockRealizeOpAgree` through
`coeffTransfer_iff_blockRealizeOp_agree`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
254--582 of `Papers/1804.04964/paper_normal.tex`. -/
theorem coeffTransfer_of_blockRealizeOpAgree (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hagree : BlockRealizeOpAgree (G := G) A B R hRA hRB f) :
    ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ := by
  intro M
  obtain ⟨N, hN⟩ := hagree M
  exact ⟨N, (coeffTransfer_iff_blockRealizeOp_agree A B R hRA hRB hAB hDim f M N).mpr hN⟩

/-- **The abstract-operator V=W predicate gives the bond-local transfer kernel.** If
the two block realization operators agree on the second tensor's partial states, then
the transfer kernel `transferCoeff A B R f M` is bond-local
(`IsBondLocalTransferKernel`). The operator agreement gives the coefficient transfer
(`coeffTransfer_of_blockRealizeOpAgree`), which the basis-change intertwining bridge
`isBondLocalTransferKernel_of_coeffTransfer`
(`TNLean.PEPS.RegionBlock.BasisChangeIntertwine`) reads as the bond locality of the
transfer kernel.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
254--582 of `Papers/1804.04964/paper_normal.tex`. -/
theorem isBondLocalTransferKernel_of_blockRealizeOpAgree (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hagree : BlockRealizeOpAgree (G := G) A B R hRA hRB f) :
    IsBondLocalTransferKernel (G := G) A B R hRB hCB f :=
  isBondLocalTransferKernel_of_coeffTransfer A B R hRA hRB hCA hCB hAB hposA hposB hDim f
    (coeffTransfer_of_blockRealizeOpAgree A B R hRA hRB hAB hDim f hagree)

end PEPS
end TNLean
