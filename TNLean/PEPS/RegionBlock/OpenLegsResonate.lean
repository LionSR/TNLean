import TNLean.PEPS.RegionBlock.ThreeBlockPhysical

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

end PEPS
end TNLean
