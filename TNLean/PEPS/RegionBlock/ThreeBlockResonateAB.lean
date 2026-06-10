import TNLean.PEPS.RegionBlock.ThreeBlockReconcile
import TNLean.PEPS.RegionBlock.ThreeBlockPhysical
import TNLean.PEPS.RegionBlock.OpenLegsResonate
import TNLean.PEPS.RegionBlock.ResonatePort2

/-!
# The cross-tensor three-block resonate chain for the normal PEPS V=W

This file builds the cross-tensor resonate chain that closes the last open step of
the general normal PEPS Fundamental Theorem per-edge gauge (arXiv:1804.04964,
Section 3, Lemma `inj_isomorph`, the step `V=W`).

The landed block-frame foundation has reduced the per-edge gauge to a single
**cross-tensor coefficient transfer**: for every inserted matrix `M` on the boundary
edge `f` of the shared red region there is a matrix `N` on the second tensor's bond
with `regionInsertedCoeff A red f M = regionInsertedCoeff B red f N` at every physical
configuration. Equivalently (`coeffTransfer_iff_basisChange_regionRegionRow`,
`TNLean.PEPS.RegionBlock.ResonatePort2`), the A↔B region basis change maps the first
tensor's bond-`f`-local region row of `M` to the second tensor's bond-`f`-local region
row of a single bond matrix `N`. The content of the step `V=W` is that this `N`
exists: the basis change preserves the bond-`f`/away-from-`f` decomposition.

The decisive geometric fact is that the red and blue blocks cross at exactly one
edge — the distinguished edge `e`, whose endpoints are the red endpoint `e.1.1` and
the blue endpoint `e.1.2`. The three-block structure is red / blue / complement with
the inserted matrix `M` on the red boundary edge `f`, exactly the edge template's
shape. The cross-tensor reading of the first tensor's coefficient through the second
tensor's red block (`regionInsertedCoeff_eq_threeBlockOpCoeff_B`,
`TNLean.PEPS.RegionBlock.ThreeBlockPhysical`) and through the second tensor's host
block (`regionInsertedCoeff_eq_blockRealizeOp_complementPartialState_B`,
`TNLean.PEPS.RegionBlock.ResonatePort`) agree because both are the first tensor's
coefficient of `M`; this is the cross-tensor resonate identity at block granularity.

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

/-! ### A1: the cross-tensor resonate identity

The first tensor's region-inserted coefficient of `M`, read through the second
tensor's `SameState`-invariant data, has two block realizations:

* the **red-side** realization, the abstract-operator three-block coefficient of the
  first tensor's red-block realization operator `blockRealizeOp A red hRA f M` read on
  the second tensor's red partial state (`regionInsertedCoeff_eq_threeBlockOpCoeff_B`,
  `TNLean.PEPS.RegionBlock.ThreeBlockPhysical`);
* the **host-side** realization, the host-block realization operator of `Mᵀ` at the
  region `univ \ red` and the boundary edge `regionBoundaryEdgeToCompl red f` read on
  the second tensor's host partial state
  (`regionInsertedCoeff_eq_blockRealizeOp_complementPartialState_B`,
  `TNLean.PEPS.RegionBlock.ResonatePort`).

Both realizations are the first tensor's coefficient of `M`, so they agree. This is
the cross-tensor `eq:resonate` at block granularity. -/

/-- **A1: the cross-tensor resonate identity.** The abstract-operator three-block
coefficient of the first tensor's red-block realization operator, read on the second
tensor's red partial state, equals the host-block realization operator of `Mᵀ` read on
the second tensor's host partial state, both as functions of the complement physical
leg at a fixed region physical leg `σ`. Both sides are the first tensor's
region-inserted coefficient of `M`: the red side by
`regionInsertedCoeff_eq_threeBlockOpCoeff_B` (and `threeBlockOpCoeff_apply`), the host
side by `regionInsertedCoeff_eq_blockRealizeOp_complementPartialState_B`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockOpCoeff_resonate_AB (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        blockRealizeOp (G := G) A R hRA f M
          ((regionInteriorBondProd (G := G) B R : ℂ) •
            regionPartialState (G := G) B R τ) σ) =
      blockRealizeOp (G := G) A (Finset.univ \ R) hCA
        (regionBoundaryEdgeToCompl (G := G) R f) M.transpose
        ((regionInteriorBondProd (G := G) B (Finset.univ \ R) : ℂ) •
          regionPartialState (G := G) B (Finset.univ \ R)
            (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)) := by
  -- Both sides equal the first tensor's region-inserted coefficient of `M`, read as a
  -- function of the complement physical leg `τ`.
  funext τ
  -- Red side: the abstract three-block operator coefficient is `coeff_A M`.
  have hred := regionInsertedCoeff_eq_threeBlockOpCoeff_B A B R hRA hAB hDim f M σ τ
  rw [threeBlockOpCoeff_apply] at hred
  -- Host side: the complement-side realization is `coeff_A M` as a function of `τ`.
  have hhost := regionInsertedCoeff_eq_blockRealizeOp_complementPartialState_B A B R hCA hAB
    hDim f M σ
  rw [← hred, congrFun hhost τ]

/-! ### B3: the M-free blue read-off coincides for A and B

The complement coupling row `threeBlockComplCoeff D bdry σcompl` is `M`-free: it
depends on the tensor only through the fused host weight (`threeBlockComplCoeff`,
`TNLean.PEPS.RegionBlock.ThreeBlockResonate2`). The blue endpoint inversion
`threeBlock_invert_blue` (`TNLean.PEPS.RegionBlock.ThreeBlockResonate2`) reads it off
the blue block's chosen left inverse, scaled by the blue interior bond product. This is
a single-tensor read-off, available at both tensors of `SameState A B`. -/

/-- **B3: the M-free blue read-off.** The blue endpoint inversion of a one-edge
blocking datum reads the complement coupling row `threeBlockComplCoeff` off the blue
block's chosen left inverse of the fused host weight, scaled by the blue interior bond
product. This is `threeBlock_invert_blue` (`TNLean.PEPS.RegionBlock.ThreeBlockResonate2`)
packaged as the residual-quantified read-off the reconcile references; it is `M`-free,
so it provides the common reference frame for the red read-off.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:inj_O->X_argument`,
lines 355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlock_blue_readoff_AB {A : Tensor G d} {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (regionInteriorBondProd (G := G) A D.blue : ℂ) •
        regionBlockedLeftInverse (G := G) A D.blue
          (regionBlockedTensorInjective_blue (A := A) (e := e) D)
          (fun σblue => regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
            (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) =
      fun bβ => threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ :=
  threeBlock_blue_readoff (A := A) (e := e) D bdry σcompl

end PEPS
end TNLean
