import TNLean.PEPS.RegionBlock.ThreeBlockResonateAB

/-!
# The host↔blue collapse of the cross-tensor three-block resonate identity

This file continues `TNLean.PEPS.RegionBlock.ThreeBlockResonateAB`, building the
**host↔blue collapse** of the cross-tensor resonate identity for the general normal
PEPS Fundamental Theorem per-edge gauge (arXiv:1804.04964, Section 3, Lemma
`inj_isomorph`, the step `V=W`).

The landed cross-tensor resonate identity `threeBlockOpCoeff_resonate_AB`
(`TNLean.PEPS.RegionBlock.ThreeBlockResonateAB`) reads the first tensor's
region-inserted coefficient of `M` through the **second** tensor's `SameState`-invariant
partial states two ways:

* the **red-side** realization, the first tensor's red-block realization operator
  `blockRealizeOp A red hRA f M` on the second tensor's red partial state;
* the **host-side** realization, the first tensor's host-block realization operator
  `blockRealizeOp A (univ \ red) hCA (toCompl f) Mᵀ` on the second tensor's host partial
  state.

The decisive geometric fact is that the host block `univ \ red` is the disjoint union of
the blue and complement blocks (`sdiff_red_eq_blue_union_complement`), and the red and
blue blocks cross at exactly the distinguished edge `e`. So the host-side reading,
written through the blue/complement split, carries the bond-paired structure on `e`
inside the blue block. The complement block is the separately invertible middle; the
landed single-tensor engine (`threeBlock_invert_blue`, `threeBlock_middle_strip`) strips
it, leaving a **blue-block reading**.

This file works entirely in **physical-configuration space** — the host complement leg
`τ` of `univ \ red` is read as the fused blue/complement leg
`threeBlockComplPhysical DB σblue σcompl` — to avoid the dependent-type casts of the
boundary-configuration spaces of the two tensors.

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

/-! ### The cross-tensor resonate identity in the three-block frame

Reading the host complement leg `τ` of `univ \ red` through the blue/complement split
`threeBlockComplPhysical DB σblue σcompl` puts the cross-tensor resonate identity
`threeBlockOpCoeff_resonate_AB` (`TNLean.PEPS.RegionBlock.ThreeBlockResonateAB`) into the
frame the single-tensor three-block engine on the second tensor consumes: the host leg is
quantified as the two separate legs `σblue`, `σcompl`. This is the substitution
`τ := threeBlockComplPhysical DB σblue σcompl`, with the second tensor's one-edge
blocking datum `DB` supplying the blue/complement fusing. -/

/-- **The cross-tensor resonate identity in the three-block frame.** Substituting the
fused blue/complement leg of the second tensor's one-edge blocking datum `DB` for the host
complement leg, the cross-tensor resonate identity reads the first tensor's
region-inserted coefficient of `M` two ways at a fixed red physical leg `σ` and split
blue/complement legs `σblue`, `σcompl`: the first tensor's red-block realization operator
on the second tensor's red partial state, and the first tensor's host-block realization
operator of `Mᵀ` on the second tensor's host partial state at the fused leg.

This is `threeBlockOpCoeff_resonate_AB`
(`TNLean.PEPS.RegionBlock.ThreeBlockResonateAB`) evaluated at
`τ := threeBlockComplPhysical DB σblue σcompl`, with `R := DB.red` the second tensor's red
region. It puts the cross-tensor identity into the three-block frame, with the host leg
read as the two separate legs the single-tensor engine on the second tensor inverts.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockOpCoeff_resonate_AB_split (A B : Tensor G d) {e : Edge G}
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e)
    (hRA : RegionBlockedTensorInjective (G := G) A DB.red)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ DB.red))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) DB.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) DB.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) DB.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) DB.complement) :
    blockRealizeOp (G := G) A DB.red hRA f M
        ((regionInteriorBondProd (G := G) B DB.red : ℂ) •
          regionPartialState (G := G) B DB.red
            (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)) σ =
      blockRealizeOp (G := G) A (Finset.univ \ DB.red) hCA
        (regionBoundaryEdgeToCompl (G := G) DB.red f) M.transpose
        ((regionInteriorBondProd (G := G) B (Finset.univ \ DB.red) : ℂ) •
          regionPartialState (G := G) B (Finset.univ \ DB.red)
            (regionDoubleComplPhysicalConfig (V := V) (d := d) DB.red σ))
        (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl) := by
  have h := threeBlockOpCoeff_resonate_AB A B DB.red hRA hCA hAB hDim f M σ
  exact congrFun h (threeBlockComplPhysical (A := B) (e := e) DB σblue σcompl)

end PEPS
end TNLean
