import TNLean.PEPS.RegionBlock.ThreeBlockPhysical
import TNLean.PEPS.RegionBlock.BlockCoeffTransfer
import TNLean.PEPS.RegionBlock.ThreeBlockTransfer

/-!
# The open-legs reformulation and the constructed bond matrix of the normal PEPS V=W

This file isolates the genuinely cross-tensor content of the general normal PEPS
Fundamental Theorem per-edge gauge (arXiv:1804.04964, Section 3, Lemma
`inj_isomorph`, the step `V=W`) at the granularity of the three injective region
blocks, reformulated on the **all-legs-open** state rather than on closed/partial
contractions.

The per-edge gauge is reduced, by the landed block-frame foundation, to the
coefficient transfer for the boundary edge `f` of the shared red region: for every
inserted matrix `M` on the first tensor's bond there is a matrix `N` on the second
tensor's bond with `coeff_A M = coeff_B N` at every physical configuration
(`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`, `bondLocal_iff_coeffTransfer`). This
file supplies the construction of that `N` and the reduction of the coefficient
transfer to a single per-leg identity.

## The open-legs reading

The block realization operator `blockRealizeOp A red hRA f M`
(`TNLean.PEPS.RegionBlock.BlockRealization`) is the tensor-independent physical
operator on the red block that realizes the first tensor's red-block matrix
insertion of `M`. Read on the **second tensor's** partial state across the region
cut — the `SameState`-invariant object — it recovers the first tensor's
region-inserted coefficient of `M` (`regionInsertedCoeff_eq_threeBlockOpCoeff_B`,
`TNLean.PEPS.RegionBlock.ThreeBlockPhysical`). This is the open-legs transport: the
realization operator built from the first tensor acts on the second tensor's column.

## The constructed bond matrix

The second tensor's region block is injective, so the first tensor's coefficient of
`M`, read as a function of the region physical leg, is the second tensor's region
blocked tensor map of a boundary-configuration row `blockTransferRow A B red f M τ`
(`regionInsertedCoeff_eq_blockTransferRow`,
`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`). The coefficient transfer is therefore
equivalent to that transferred row being the second tensor's own region row
`regionRegionRow B red f N τ` of a single bond matrix `N` on `f`, at every complement
physical leg. This is the bond-level content of the step `V=W`, isolated here as a
single per-leg identity of the transferred row.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, the step `V=W`, lines 355--486 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Target 1--3: the open-legs reading of the first tensor's coefficient

The block realization operator built from the first tensor `A`, read on the second
tensor's partial state across the region cut, recovers the first tensor's
region-inserted coefficient of `M`. This is the landed transport
`regionInsertedCoeff_eq_threeBlockOpCoeff_B` (Targets 2--3 of
`TNLean.PEPS.RegionBlock.ThreeBlockPhysical`) restated as an identity of the
open-legs coefficient function. The single cross-tensor step is the `SameState`
invariance of the partial state; everything else is single-tensor block mechanics. -/

/-- **The open-legs reading of the first tensor's coefficient.** The first tensor's
region-inserted coefficient of `M`, read as a function of the region physical leg, is
the first tensor's block realization operator of `M` applied to the interior-bond
multiple of the **second** tensor's partial state across the region cut. This is the
open-legs transport: the realization operator built from `A` reads `A`'s coefficient
off `B`'s `SameState`-invariant column.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_blockRealizeOp_regionPartialState_B (A B : Tensor G d)
    (R : Finset V) (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (fun σ : RegionPhysicalConfig (V := V) (d := d) R =>
        regionInsertedCoeff (G := G) A R f M σ τ) =
      blockRealizeOp (G := G) A R hRA f M
        ((regionInteriorBondProd (G := G) B R : ℂ) • regionPartialState (G := G) B R τ) := by
  rw [← regionInteriorBondProd_congr A B R hDim,
    blockRealizeOp_regionPartialState_B_eq_regionInsertedCoeff A B R hRA hAB f M τ]

/-! ### Target 4: the coefficient transfer is the transferred row being a region row

The first tensor's region-inserted coefficient of `M`, read as a function of the
region physical leg, is the second tensor's region blocked tensor map of the
transferred row `blockTransferRow A B red f M τ` (the second tensor's region left
inverse of that coefficient, `regionInsertedCoeff_eq_blockTransferRow`,
`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`). The second tensor's coefficient of a
bond matrix `N` factors through the **same** injective region block, of the region
row `regionRegionRow B red f N τ`. So the coefficient transfer `coeff_A M = coeff_B N`
is equivalent to the transferred row coinciding with the second tensor's region row of
`N` at every complement leg. This isolates the cross-tensor content as a single
per-leg identity of the transferred row, with the bond matrix `N` carried directly. -/

/-- **The coefficient transfer is the transferred row being a region row.** For a bond
matrix `N`, the first tensor's region-inserted coefficient of `M` equals the second
tensor's of `N` at every physical configuration if and only if the transferred row
`blockTransferRow A B red f M τ` is the second tensor's region row
`regionRegionRow B red f N τ` at every complement physical leg.

Both coefficients factor through the second tensor's injective region blocked tensor
map (`hRB`): the first tensor's of `M` of the transferred row by
`regionInsertedCoeff_eq_blockTransferRow`, the second tensor's of `N` of the region
row by `regionInsertedCoeff_eq_region_blockedMap`. The forward direction descends the
coefficient equality through the injective block; the backward direction reblocks the
row equality. This presents the coefficient transfer as the single per-leg identity of
the transferred row — the bond-level content of the step `V=W`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem coeffTransfer_iff_blockTransferRow_eq_regionRegionRow (A B : Tensor G d)
    (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    (∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f N σ τ) ↔
      ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
        blockTransferRow A B R hRB f M τ = regionRegionRow (G := G) B R f N τ := by
  constructor
  · -- Forward: equal coefficients descend through the injective region block to equal rows.
    intro hcoeff τ
    have hblock : regionBlockedTensorMap (G := G) B R (blockTransferRow A B R hRB f M τ) =
        regionBlockedTensorMap (G := G) B R (regionRegionRow (G := G) B R f N τ) := by
      funext σ
      rw [← regionInsertedCoeff_eq_blockTransferRow A B R hRB hCA hCB hAB hposA hposB hDim f M σ τ,
        ← regionInsertedCoeff_eq_region_blockedMap B R f N σ τ]
      exact hcoeff σ τ
    exact regionBlockedTensorMap_injective_of_injective (G := G) B R hRB hblock
  · -- Backward: equal rows reblock to equal coefficients.
    intro hrow σ τ
    rw [regionInsertedCoeff_eq_blockTransferRow A B R hRB hCA hCB hAB hposA hposB hDim f M σ τ,
      hrow τ, ← regionInsertedCoeff_eq_region_blockedMap B R f N σ τ]

/-! ### The transferred-row region-row predicate

The single residual open fact of the general normal PEPS per-edge gauge, isolated as
a per-leg identity of the transferred row. The predicate asserts that for every
inserted matrix `M` on the boundary edge `f` of the red region there is a bond matrix
`N` on the second tensor whose region row `regionRegionRow B red f N τ` is the
transferred row `blockTransferRow A B red f M τ` at every complement physical leg.

By `coeffTransfer_iff_blockTransferRow_eq_regionRegionRow` this predicate is exactly
the coefficient transfer, hence (`bondLocal_iff_coeffTransfer`,
`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`) the bond locality of the transfer
kernel. The region row `regionRegionRow B red f N τ` is the incident-matrix coupling
of `N` on the bond legs against the second tensor's complement weights
(`regionRegionRow_eq_rowInsertF`,
`TNLean.PEPS.RegionBlock.BlockRealization`), so the predicate is the bond-level
content of the source step `V=W`: the cross-tensor transferred row couples through the
boundary bond `f` only. -/

/-- **The transferred-row region-row predicate.** For every inserted matrix `M` on the
boundary edge `f`, there is a bond matrix `N` on the second tensor whose region row
`regionRegionRow B red f N` is the transferred row `blockTransferRow A B red f M` at
every complement physical leg.

This is the open-legs form of the block step `V=W`: the second tensor's region left
inverse of the first tensor's `M`-coefficient is the second tensor's own region row of
a single bond matrix `N`, i.e. couples through the bond `f` only. -/
def TransferRowIsRegionRow (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : Prop :=
  ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
    ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
      ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
        blockTransferRow A B R hRB f M τ = regionRegionRow (G := G) B R f N τ

/-- **The transferred-row region-row predicate gives the coefficient transfer.** If
every transferred row is the second tensor's region row of some bond matrix `N`, then
for every inserted matrix `M` there is a bond matrix `N` whose region-inserted
coefficient matches the first tensor's of `M` at every physical configuration. This
unpacks `TransferRowIsRegionRow` through
`coeffTransfer_iff_blockTransferRow_eq_regionRegionRow`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem coeffTransfer_of_transferRowIsRegionRow (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hrow : TransferRowIsRegionRow (G := G) A B R hRB f) :
    ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ := by
  intro M
  obtain ⟨N, hN⟩ := hrow M
  exact ⟨N, (coeffTransfer_iff_blockTransferRow_eq_regionRegionRow A B R hRB hCA hCB hAB
    hposA hposB hDim f M N).mpr hN⟩

/-- **Bond locality is the transferred-row region-row predicate.** The transfer kernel
of every inserted matrix on the boundary edge `f` is bond-local
(`IsBondLocalTransferKernel`) if and only if every transferred row is the second
tensor's region row of some bond matrix `N`. Both directions are
`coeffTransfer_iff_blockTransferRow_eq_regionRegionRow` quantified over `M`, against the
bond-locality–coefficient-transfer equivalence `bondLocal_iff_coeffTransfer`
(`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`).

This restates the single residual open fact of the per-edge gauge as the geometric
per-leg identity of the transferred row.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem isBondLocalTransferKernel_iff_transferRowIsRegionRow (A B : Tensor G d)
    (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    IsBondLocalTransferKernel (G := G) A B R hRB hCB f ↔
      TransferRowIsRegionRow (G := G) A B R hRB f := by
  rw [bondLocal_iff_coeffTransfer A B R hRA hRB hCA hCB hAB hposA hposB hDim f]
  refine forall_congr' (fun M => exists_congr (fun N => ?_))
  exact coeffTransfer_iff_blockTransferRow_eq_regionRegionRow A B R hRB hCA hCB hAB
    hposA hposB hDim f M N

/-- **Bond locality from the transferred-row region-row predicate.** If every
transferred row is the second tensor's region row of some bond matrix, then the
transfer kernel is bond-local (`IsBondLocalTransferKernel`). This is the forward
read-off of `isBondLocalTransferKernel_iff_transferRowIsRegionRow`, the form the
per-edge gauge `SharedNormalEdgeBlockingData.exists_regionEdgeGauge`
(`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`) consumes.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem isBondLocalTransferKernel_of_transferRowIsRegionRow (A B : Tensor G d)
    (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hrow : TransferRowIsRegionRow (G := G) A B R hRB f) :
    IsBondLocalTransferKernel (G := G) A B R hRB hCB f :=
  (isBondLocalTransferKernel_iff_transferRowIsRegionRow A B R hRA hRB hCA hCB hAB
    hposA hposB hDim f).mpr hrow

/-! ### The transferred-row region-row predicate spelled out as a bond-`f` coupling

The second tensor's region row `regionRegionRow B red f N τ` is the row insertion of
`N` on the boundary edge `f` of the second tensor's complement weight row
(`regionRegionRow_eq_rowInsertF`, `TNLean.PEPS.RegionBlock.BlockRealization`): it
couples the two boundary configurations through their `f`-legs via `N` and contracts
the residual legs by the identity. So the transferred-row region-row predicate is
exactly the statement that the transferred row is a bond-`f` coupling of a single
matrix `N` against the second tensor's complement weight row. -/

/-- **The transferred-row region-row predicate as a bond-`f` coupling.** The
transferred-row region-row predicate holds if and only if, for every inserted matrix
`M`, there is a bond matrix `N` whose row insertion on the boundary edge `f` of the
second tensor's complement weight row is the transferred row, at every complement
physical leg. This spells out the predicate as the bond-`f` locality of the
transferred row: it couples the boundary configurations through their `f`-legs only,
through the single matrix `N`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem transferRowIsRegionRow_iff_rowInsertF (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    TransferRowIsRegionRow (G := G) A B R hRB f ↔
      ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
        ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
          ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
            blockTransferRow A B R hRB f M τ =
              rowInsertF (G := G) B R f N (regionComplementWeightRow (G := G) B R τ) := by
  unfold TransferRowIsRegionRow
  refine forall_congr' (fun M => exists_congr (fun N => forall_congr' (fun τ => ?_)))
  rw [regionRegionRow_eq_rowInsertF B R f N τ]

end PEPS
end TNLean
