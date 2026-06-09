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

/-! ### The four block-injectivity facts the backbone consumes

Every backbone lemma of `TNLean.PEPS.RegionBlock.BlockCoeffTransfer` at the red
region needs the four blocked-tensor injectivities
`RegionBlockedTensorInjective A red`, `RegionBlockedTensorInjective A (univ \ red)`,
`RegionBlockedTensorInjective B red`, and `RegionBlockedTensorInjective B (univ \ red)`.
The region injectivities are the blocking-data fields; the host-block injectivities
are the union lemma `regionBlockedTensorInjective_compl_red`. For the second tensor
the shared region equalities transport the read-offs to the shared red region. -/

/-- The first tensor's red block is blocked-tensor injective. -/
theorem regionInjective_red_A (D : SharedNormalEdgeBlockingData A B e) :
    RegionBlockedTensorInjective (G := G) A D.red :=
  regionBlockedTensorInjective_red (A := A) (e := e) D.dataA

/-- The second tensor's red block is blocked-tensor injective. The shared red region
equality transports the read-off to the shared red region. -/
theorem regionInjective_red_B (D : SharedNormalEdgeBlockingData A B e) :
    RegionBlockedTensorInjective (G := G) B D.red := by
  rw [SharedNormalEdgeBlockingData.red, ← D.red_eq]
  exact regionBlockedTensorInjective_red (A := B) (e := e) D.dataB

/-- The first tensor's host block `univ \ red` is blocked-tensor injective, by the
union lemma applied to the blue and complement blocks. -/
theorem regionInjective_compl_red_A (D : SharedNormalEdgeBlockingData A B e)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) :
    RegionBlockedTensorInjective (G := G) A (Finset.univ \ D.red) :=
  regionBlockedTensorInjective_compl_red (A := A) (e := e) D.dataA hposA

/-- The second tensor's host block `univ \ red` is blocked-tensor injective, by the
union lemma applied to its blue and complement blocks, transported to the shared red
region. -/
theorem regionInjective_compl_red_B (D : SharedNormalEdgeBlockingData A B e)
    (hposB : ∀ g : Edge G, 0 < B.bondDim g) :
    RegionBlockedTensorInjective (G := G) B (Finset.univ \ D.red) := by
  rw [SharedNormalEdgeBlockingData.red, ← D.red_eq]
  exact regionBlockedTensorInjective_compl_red (A := B) (e := e) D.dataB hposB

end SharedNormalEdgeBlockingData

/-! ### Bond locality of the transfer kernel

The one fact the block-frame foundation does not supply: the transfer kernel
`transferCoeff A B red f M` couples the two boundary configurations only through
their legs on the boundary edge `f`. Concretely, for every inserted matrix `M` the
kernel is the incident-matrix kernel `incidentKernel B red f N` of some bond matrix
`N`. This is the block-level content of the source step `V=W`, forced by the resonate
identity and the full injectivity of both blocked endpoints. It is isolated here as
the predicate `IsBondLocalTransferKernel`. -/

/-- **Bond locality of the transfer kernel.** For every inserted matrix `M` on the
boundary edge `f` of the red region, the transfer kernel
`transferCoeff A B red hRB hCB f M` (the doubly-indexed kernel read off the two
blocked left inverses of the second tensor) is the incident-matrix kernel
`incidentKernel B red f N` of some bond matrix `N` on `f`. Equivalently, the kernel
depends on the two boundary configurations only through their legs on `f`.

This is the residual open content of the block-frame coefficient transfer
(arXiv:1804.04964, Section 3, the step `V=W`). The reconcile-is-transfer bridge
`transferCoeff_eq_incidentKernel_iff_coeff_eq`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) shows that this predicate is equivalent
to the coefficient transfer `∀ M, ∃ N, ∀ σ τ, coeff_A M = coeff_B N` once the four
block injectivities and positive bond dimensions hold.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
def IsBondLocalTransferKernel (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : Prop :=
  ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
    ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
      transferCoeff (G := G) A B R hRB hCB f M = incidentKernel (G := G) B R f N

/-- **Bond locality gives the coefficient transfer.** If the transfer kernel of every
inserted matrix on the boundary edge `f` of the red region is bond-local, then the
first tensor's region-inserted coefficient of every `M` is realized by a bond matrix
`N` on the second tensor. This is the reconcile-is-transfer bridge
`transferCoeff_eq_incidentKernel_iff_coeff_eq`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) read in the forward direction.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem coeffTransfer_of_bondLocal (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hbond : IsBondLocalTransferKernel (G := G) A B R hRB hCB f) :
    ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ := by
  intro M
  obtain ⟨N, hN⟩ := hbond M
  refine ⟨N, ?_⟩
  exact (transferCoeff_eq_incidentKernel_iff_coeff_eq A B R hRA hRB hCA hCB hAB
    hposA hposB hDim f M N).mp hN

/-! ### The per-edge gauge from bond locality in both directions

Assembling the two coefficient transfers from the two-directional bond locality and
feeding them, with the multiplicative forward choice, to the conditional per-edge
gauge `exists_regionEdgeGauge_of_coeffTransfer`
(`TNLean.PEPS.RegionBlock.RegionReconcile`). All four block injectivities come from
the shared one-edge blocking data and positive bond dimensions; the forward
multiplicativity `hmul` and the two-directional bond locality are the remaining
hypotheses, the open content `V=W` of the block frame. -/

/-- The forward coefficient transfer of a shared one-edge blocking datum, derived from
the `A → B` bond locality. For each inserted matrix `M` on the boundary edge `f` of
the shared red region there is a bond matrix `N` on the second tensor whose
region-inserted coefficient matches. -/
theorem SharedNormalEdgeBlockingData.coeffTransferAB
    (D : SharedNormalEdgeBlockingData A B e)
    (hAB : SameState A B)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (hbondAB : IsBondLocalTransferKernel (G := G) A B D.red
      D.regionInjective_red_B (D.regionInjective_compl_red_B hposB) f) :
    ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) D.red)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ D.red)),
          regionInsertedCoeff (G := G) A D.red f M σ τ =
            regionInsertedCoeff (G := G) B D.red f N σ τ :=
  coeffTransfer_of_bondLocal A B D.red D.regionInjective_red_A D.regionInjective_red_B
    (D.regionInjective_compl_red_A hposA) (D.regionInjective_compl_red_B hposB) hAB
    hposA hposB hDim f hbondAB

/-- The backward coefficient transfer of a shared one-edge blocking datum, derived from
the `B → A` bond locality (the shared datum with the two tensors swapped). For each
inserted matrix `N` on the boundary edge `f` there is a bond matrix `M` on the first
tensor whose region-inserted coefficient matches. -/
theorem SharedNormalEdgeBlockingData.coeffTransferBA
    (D : SharedNormalEdgeBlockingData A B e)
    (hBA : SameState B A)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hDim : B.bondDim = A.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (hbondBA : IsBondLocalTransferKernel (G := G) B A D.red
      D.regionInjective_red_A (D.regionInjective_compl_red_A hposA) f) :
    ∀ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
      ∃ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) D.red)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ D.red)),
          regionInsertedCoeff (G := G) B D.red f N σ τ =
            regionInsertedCoeff (G := G) A D.red f M σ τ :=
  coeffTransfer_of_bondLocal B A D.red D.regionInjective_red_B D.regionInjective_red_A
    (D.regionInjective_compl_red_B hposB) (D.regionInjective_compl_red_A hposA) hBA
    hposB hposA hDim f hbondBA

/-- **The per-edge gauge from two-directional bond locality.** Given a shared one-edge
blocking datum for the two tensors of `SameState A B`, positive bond dimensions,
matched bond dimensions, two-directional bond locality of the transfer kernel on the
boundary edge `f` of the shared red region, and the multiplicative forward choice, the
forward per-edge matrix transfer on `f` is conjugation by an invertible gauge matrix
`Z`, and the bond dimensions on `f` coincide.

No single-vertex injectivity is used: the four block injectivities come from the
shared blocking data and the union lemma, the two coefficient transfers come from the
two-directional bond locality, and the read-off is
`exists_regionEdgeGauge_of_coeffTransfer`
(`TNLean.PEPS.RegionBlock.RegionReconcile`). The bond locality and the forward
multiplicativity are the remaining hypotheses, the open content `V=W` of the block
frame, documented in `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem SharedNormalEdgeBlockingData.exists_regionEdgeGauge
    (D : SharedNormalEdgeBlockingData A B e)
    (hAB : SameState A B)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (hbondAB : IsBondLocalTransferKernel (G := G) A B D.red
      D.regionInjective_red_B (D.regionInjective_compl_red_B hposB) f)
    (hbondBA : IsBondLocalTransferKernel (G := G) B A D.red
      D.regionInjective_red_A (D.regionInjective_compl_red_A hposA) f)
    (hmul : ∀ M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      coeffTransferMap (G := G) A B D.red f
          (D.coeffTransferAB hAB hposA hposB hDim f hbondAB) (M * M') =
        coeffTransferMap (G := G) A B D.red f
            (D.coeffTransferAB hAB hposA hposB hDim f hbondAB) M *
          coeffTransferMap (G := G) A B D.red f
            (D.coeffTransferAB hAB hposA hposB hDim f hbondAB) M') :
    ∃ hEdge : A.bondDim f.1 = B.bondDim f.1,
      ∃ Z : GL (Fin (B.bondDim f.1)) ℂ,
        ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
          (regionInsertionTransfer_of_coeffTransfer A B D.red f
              D.regionInjective_red_B (D.regionInjective_compl_red_B hposB) hAB hposB hDim
              (D.coeffTransferAB hAB hposA hposB hDim f hbondAB)
              (D.coeffTransferBA hAB.symm hposA hposB hDim.symm f hbondBA) hmul).fwd M =
            (Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
              ((Z⁻¹ : GL (Fin (B.bondDim f.1)) ℂ) :
                Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :=
  exists_regionEdgeGauge_of_coeffTransfer A B D.red f
    D.regionInjective_red_A (D.regionInjective_compl_red_A hposA)
    D.regionInjective_red_B (D.regionInjective_compl_red_B hposB)
    hAB hposA hposB hDim
    (D.coeffTransferAB hAB hposA hposB hDim f hbondAB)
    (D.coeffTransferBA hAB.symm hposA hposB hDim.symm f hbondBA) hmul

end PEPS
end TNLean
