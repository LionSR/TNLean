import TNLean.PEPS.RegionBlock.BlockRealization
import TNLean.PEPS.RegionBlock.ThreeBlockReconcile
import TNLean.PEPS.RegionBlock.UnionInjectivity

/-!
# The basis-change intertwining of the cross-tensor transfer kernel

This file proves the **basis-change intertwining**, the last open obligation of the
general normal PEPS Fundamental Theorem per-edge gauge (arXiv:1804.04964, Section 3,
Lemma `inj_isomorph`, the step `V=W`). It is the cross-tensor content that
`isBondLocalTransferKernel_of_basisChange_intertwine`
(`TNLean.PEPS.RegionBlock.BlockRealization`) consumes: for every inserted matrix `M`
on the boundary edge `f` of the red region there is a matrix `N` on the second
tensor's bond such that the A↔B region basis change `regionBasisChange` conjugates
the first tensor's row insertion of `M` to the second tensor's row insertion of `N`,
on the second tensor's partial-state rows.

## The reblock-level reformulation

The first tensor's region blocked tensor map is injective (`hRA`), so the intertwining
holds if and only if its two sides have the same first-tensor region block image. The
two block images are computed directly: the row-insertion side is the interior bond
multiple of the first tensor's region-inserted coefficient
(`regionInsertedCoeff_eq_crossExpansion`), and the basis-change side is, on the common
range, the second tensor's region block of its own row insertion of `N`
(`regionBlockedTensorMap_basisChange_eq_of_mem_range`), which is the interior bond
multiple of the second tensor's region-inserted coefficient of `N`. With matched
interior bond products (`hDim`), the intertwining is **equivalent** to the coefficient
equality `coeff_A M = coeff_B N` at every physical configuration. This is the
unconditional bridge from the cross-tensor intertwining to the block-frame coefficient
transfer the per-edge gauge consumes.

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

/-! ### Step 1: the basis change round-trips through the common range

The first tensor's region blocked tensor map of the basis change of a second-tensor
row whose second-tensor block image lies in the common range returns the second
tensor's region blocked tensor map of the row. This is
`regionBlockedTensorMap_basisChange_eq_of_mem_range`
(`TNLean.PEPS.RegionBlock.BlockRealization`) packaged for the rows that appear in the
intertwining: the second tensor's row insertion of `N` of the partial-state row, whose
second-tensor block image lies in the second tensor's region range, which is the common
range across `SameState`. -/

/-- **The N-inserted partial-state row's second block image lies in the common range.**
The second tensor's region blocked tensor map of the row insertion of `N` of the
second tensor's partial-state row lies in the range of the first tensor's region
blocked tensor map. Its second-tensor block image lies in the second tensor's region
range, which coincides with the first tensor's region range across `SameState`
(`range_regionBlockedTensorMap_eq_of_sameState`,
`TNLean.PEPS.RegionBlock.BlockRangeCoincidence`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorMap_rowInsertF_partialStateRowB_mem_range (A B : Tensor G d)
    (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionBlockedTensorMap (G := G) B R
        (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ)) ∈
      LinearMap.range (regionBlockedTensorMap (G := G) A R) := by
  rw [range_regionBlockedTensorMap_eq_of_sameState A B R hAB hCA hCB hposA hposB hDim]
  exact LinearMap.mem_range_self _ _

/-- **The basis change reblocks the N-inserted partial-state row to the second tensor's
block.** The first tensor's region blocked tensor map of the basis change of the second
tensor's row insertion of `N` of the partial-state row equals the second tensor's
region blocked tensor map of that row insertion. The basis change reads the row off the
second tensor's region block and reblocks through the first tensor's region block; on
the common range (where the N-inserted partial-state row's second block image lies) the
reblocking returns the second tensor's block image.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorMap_basisChange_rowInsertF_partialStateRowB (A B : Tensor G d)
    (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionBlockedTensorMap (G := G) A R
        (regionBasisChange (G := G) A B R hRA
          (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ))) =
      regionBlockedTensorMap (G := G) B R
        (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ)) :=
  regionBlockedTensorMap_basisChange_eq_of_mem_range A B R hRA _
    (regionBlockedTensorMap_rowInsertF_partialStateRowB_mem_range A B R hRB hCA hCB hAB
      hposA hposB hDim f N τ)

/-! ### Step 2: the two block images of the intertwining

The first tensor's region blocked tensor map of each side of the intertwining is the
interior bond multiple of a region-inserted coefficient. The row-insertion side is the
first tensor's region-inserted coefficient of `M`; the basis-change side is the second
tensor's region-inserted coefficient of `N`. -/

/-- **The block image of the row-insertion side.** The first tensor's region blocked
tensor map of the row insertion of `M` of the basis-changed second-tensor partial-state
row, scaled by the first tensor's interior bond product, is the first tensor's
region-inserted coefficient of `M`. This is the cross-tensor expansion
`regionInsertedCoeff_eq_crossExpansion`
(`TNLean.PEPS.RegionBlock.BlockRealization`) read forwards.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_regionBlockedTensorMap_rowInsertF_basisChange
    (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hAB : SameState A B) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (regionInteriorBondProd (G := G) A R : ℂ) •
        regionBlockedTensorMap (G := G) A R
          (rowInsertF (G := G) A R f M
            (regionBasisChange (G := G) A B R hRA
              (partialStateRowB (G := G) B R hRB τ))) =
      fun σ => regionInsertedCoeff (G := G) A R f M σ τ :=
  (regionInsertedCoeff_eq_crossExpansion A B R hRA hRB hAB hposB f M τ).symm

/-- **The block image of the N-side.** The second tensor's region blocked tensor map of
the row insertion of `N` of the second tensor's partial-state row, scaled by the second
tensor's interior bond product, is the second tensor's region-inserted coefficient of
`N`. This is the B-analogue of KEY IDENTITY 1
(`blockRealizeOp_regionPartialState_eq_regionInsertedCoeff`, second tensor) with the
partial state expanded through the second tensor's region block.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_regionBlockedTensorMap_rowInsertF_partialStateRowB
    (B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (regionInteriorBondProd (G := G) B R : ℂ) •
        regionBlockedTensorMap (G := G) B R
          (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ)) =
      fun σ => regionInsertedCoeff (G := G) B R f N σ τ := by
  rw [← blockRealizeOp_regionPartialState_eq_regionInsertedCoeff (G := G) B R hRB f N τ,
    map_smul, blockRealizeOp_apply,
    ← regionBlockedTensorMap_partialStateRowB (G := G) B R hRB hposB τ,
    regionBlockedLeftInverse_apply_regionBlockedTensorMap]

/-! ### The intertwining is equivalent to the coefficient equality

Inverting the first tensor's region block (injective, `hRA`), the intertwining of the
two row insertions on a partial-state row holds if and only if their two first-tensor
region block images coincide. The block images are the interior bond multiples of the
two region-inserted coefficients (Step 2); with matched interior bond products (`hDim`)
the intertwining is equivalent to the coefficient equality `coeff_A M = coeff_B N` at
every region physical configuration. This unconditional equivalence is the bridge
between the cross-tensor intertwining and the block-frame coefficient transfer. -/

/-- **The intertwining at a single complement leg is the coefficient equality there.**
For a fixed complement physical configuration `τ`, the first tensor's row insertion of
`M` of the basis-changed partial-state row equals the basis change of the second
tensor's row insertion of `N` of the partial-state row, if and only if the first
tensor's region-inserted coefficient of `M` equals the second tensor's of `N` at every
region physical configuration with that `τ`.

The forward direction reblocks both sides through the first tensor's region block
(injective by `hRA`) and reads off the two region-inserted coefficients (Step 2,
matched interior bond products by `hDim`); the backward direction reblocks the
coefficient equality back through the injective region block.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem rowInsertF_basisChange_eq_iff_regionInsertedCoeff_eq (A B : Tensor G d)
    (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    rowInsertF (G := G) A R f M
        (regionBasisChange (G := G) A B R hRA (partialStateRowB (G := G) B R hRB τ)) =
      regionBasisChange (G := G) A B R hRA
        (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ)) ↔
      ∀ σ : RegionPhysicalConfig (V := V) (d := d) R,
        regionInsertedCoeff (G := G) A R f M σ τ =
          regionInsertedCoeff (G := G) B R f N σ τ := by
  -- The interior bond product is positive, hence nonzero, on the first tensor.
  have hposA' : 0 < regionInteriorBondProd (G := G) A R :=
    regionInteriorBondProd_pos (G := G) A R hposA
  have hne : (regionInteriorBondProd (G := G) A R : ℂ) ≠ 0 := by exact_mod_cast hposA'.ne'
  -- The two block images, scaled by the first tensor's interior bond product.
  have hLHS : (regionInteriorBondProd (G := G) A R : ℂ) •
      regionBlockedTensorMap (G := G) A R
        (rowInsertF (G := G) A R f M
          (regionBasisChange (G := G) A B R hRA (partialStateRowB (G := G) B R hRB τ))) =
      fun σ => regionInsertedCoeff (G := G) A R f M σ τ :=
    regionInteriorBondProd_smul_regionBlockedTensorMap_rowInsertF_basisChange A B R hRA hRB
      hAB hposB f M τ
  have hRHS : (regionInteriorBondProd (G := G) A R : ℂ) •
      regionBlockedTensorMap (G := G) A R
        (regionBasisChange (G := G) A B R hRA
          (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ))) =
      fun σ => regionInsertedCoeff (G := G) B R f N σ τ := by
    rw [regionBlockedTensorMap_basisChange_rowInsertF_partialStateRowB A B R hRA hRB hCA hCB
        hAB hposA hposB hDim f N τ,
      regionInteriorBondProd_congr A B R hDim,
      regionInteriorBondProd_smul_regionBlockedTensorMap_rowInsertF_partialStateRowB B R hRB
        hposB f N τ]
  constructor
  · -- Forward: equal rows give equal block images, hence equal coefficients.
    intro hrow
    have hblock : regionBlockedTensorMap (G := G) A R
        (rowInsertF (G := G) A R f M
          (regionBasisChange (G := G) A B R hRA (partialStateRowB (G := G) B R hRB τ))) =
      regionBlockedTensorMap (G := G) A R
        (regionBasisChange (G := G) A B R hRA
          (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ))) := by
      rw [hrow]
    have hcoeff : (fun σ => regionInsertedCoeff (G := G) A R f M σ τ) =
        (fun σ => regionInsertedCoeff (G := G) B R f N σ τ) := by
      rw [← hLHS, ← hRHS, hblock]
    exact fun σ => congrFun hcoeff σ
  · -- Backward: equal coefficients give equal block images, then invert the block.
    intro hcoeff
    have hcoeff' : (fun σ => regionInsertedCoeff (G := G) A R f M σ τ) =
        (fun σ => regionInsertedCoeff (G := G) B R f N σ τ) := funext hcoeff
    have hblock : regionBlockedTensorMap (G := G) A R
        (rowInsertF (G := G) A R f M
          (regionBasisChange (G := G) A B R hRA (partialStateRowB (G := G) B R hRB τ))) =
      regionBlockedTensorMap (G := G) A R
        (regionBasisChange (G := G) A B R hRA
          (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ))) := by
      have := hLHS.trans (hcoeff'.trans hRHS.symm)
      exact smul_right_injective _ hne this
    exact regionBlockedTensorMap_injective_of_injective (G := G) A R hRA hblock

/-! ### The full intertwining hypothesis is the coefficient transfer

Quantifying the single-leg equivalence over every complement physical configuration,
the existence (for a fixed `N`) of the intertwining at every complement leg is the
coefficient equality `coeff_A M = coeff_B N` at every physical configuration. Adding
the outer existential over `N` (per inserted `M`) gives the equivalence between the
intertwining hypothesis the kernel reduction
`isBondLocalTransferKernel_of_basisChange_intertwine`
(`TNLean.PEPS.RegionBlock.BlockRealization`) consumes and the block-frame coefficient
transfer the per-edge gauge needs. This closes the cross-tensor reformulation: the open
content `V=W` is now exactly the coefficient transfer, with the intertwining a
mechanical repackaging. -/

/-- **The intertwining for a fixed `N` is the coefficient equality of `M` and `N`.**
For a fixed matrix `N`, the first tensor's row insertion of `M` of the basis-changed
partial-state row equals the basis change of the second tensor's row insertion of `N`
of the partial-state row at every complement physical configuration, if and only if
the first tensor's region-inserted coefficient of `M` equals the second tensor's of `N`
at every physical configuration. This is the single-leg equivalence
`rowInsertF_basisChange_eq_iff_regionInsertedCoeff_eq` quantified over the complement
leg.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem rowInsertF_basisChange_forall_eq_iff_regionInsertedCoeff_eq (A B : Tensor G d)
    (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    (∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
        rowInsertF (G := G) A R f M
            (regionBasisChange (G := G) A B R hRA (partialStateRowB (G := G) B R hRB τ)) =
          regionBasisChange (G := G) A B R hRA
            (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ))) ↔
      ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
        regionInsertedCoeff (G := G) A R f M σ τ =
          regionInsertedCoeff (G := G) B R f N σ τ := by
  constructor
  · intro h σ τ
    exact (rowInsertF_basisChange_eq_iff_regionInsertedCoeff_eq A B R hRA hRB hCA hCB hAB
      hposA hposB hDim f M N τ).mp (h τ) σ
  · intro h τ
    exact (rowInsertF_basisChange_eq_iff_regionInsertedCoeff_eq A B R hRA hRB hCA hCB hAB
      hposA hposB hDim f M N τ).mpr (fun σ => h σ τ)

/-- **The intertwining hypothesis is the coefficient transfer.** For every inserted
matrix `M` on the boundary edge `f` there is a matrix `N` on the second tensor's bond
intertwining the two row insertions (the hypothesis of
`isBondLocalTransferKernel_of_basisChange_intertwine`,
`TNLean.PEPS.RegionBlock.BlockRealization`) if and only if for every `M` there is an
`N` whose region-inserted coefficient matches at every physical configuration (the
block-frame coefficient transfer the per-edge gauge consumes). Both quantify the same
matrix `N`; the equivalence is per-`N` the single-leg reblock reformulation.

This makes the residual open content of the general normal PEPS per-edge gauge exactly
the coefficient transfer: the intertwining is its mechanical repackaging through the
basis change, with no single-vertex injectivity.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem basisChange_intertwine_iff_coeffTransfer (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    (∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
        ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
          ∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
            rowInsertF (G := G) A R f M
                (regionBasisChange (G := G) A B R hRA (partialStateRowB (G := G) B R hRB τ)) =
              regionBasisChange (G := G) A B R hRA
                (rowInsertF (G := G) B R f N (partialStateRowB (G := G) B R hRB τ))) ↔
      ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
        ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
          ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
            (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
            regionInsertedCoeff (G := G) A R f M σ τ =
              regionInsertedCoeff (G := G) B R f N σ τ := by
  refine forall_congr' (fun M => exists_congr (fun N => ?_))
  exact rowInsertF_basisChange_forall_eq_iff_regionInsertedCoeff_eq A B R hRA hRB hCA hCB hAB
    hposA hposB hDim f M N

/-- **Bond locality from the coefficient transfer, via the basis-change intertwining.**
If for every inserted matrix `M` on the boundary edge `f` there is a matrix `N` whose
region-inserted coefficient matches, then the transfer kernel is bond-local
(`IsBondLocalTransferKernel`). The coefficient transfer gives the intertwining
(`basisChange_intertwine_iff_coeffTransfer`), which
`isBondLocalTransferKernel_of_basisChange_intertwine`
(`TNLean.PEPS.RegionBlock.BlockRealization`) reads as the bond locality of the transfer
kernel.

This is the cross-tensor route to the bond locality through the basis change, parallel
to the direct route `coeffTransfer_iff_transferCoeff_incidentForm`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`): both close once the coefficient transfer
is supplied.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem isBondLocalTransferKernel_of_coeffTransfer (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (htransfer : ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ) :
    IsBondLocalTransferKernel (G := G) A B R hRB hCB f :=
  isBondLocalTransferKernel_of_basisChange_intertwine A B R hRA hRB hCA hCB hAB hposA hposB
    hDim f
    ((basisChange_intertwine_iff_coeffTransfer A B R hRA hRB hCA hCB hAB hposA hposB hDim f).mpr
      htransfer)

end PEPS
end TNLean
