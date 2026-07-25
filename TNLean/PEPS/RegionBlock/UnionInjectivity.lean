/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.ThreeBlockResonate2
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral2

/-!
# Injectivity of the union of two injective region blocks

This file proves the union lemma of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`): the contraction of injective tensors over the
union of two disjoint injective regions is again injective. The load-bearing
instance is the union of the blue and complement blocks of a
`NormalEdgeBlockingData`, whose union is the set complement of the red block
(`univ \ red`). The three-block gauge chain needs the host block `univ \ red` to be
blocked-tensor injective, which this file supplies from injectivity of the blue and
complement blocks individually.

The proof is the source's two-step inverse application. Suppose a coefficient
family `c` annihilates the blocked-region weight family of `univ \ red`. Reading the
physical leg of `univ \ red` as a fused blue/complement pair
(`threeBlockComplPhysical`, a bijection onto `univ \ red` legs), the core
factorization `regionInteriorBondProd_smul_threeBlockComplWeight_eq` rewrites the
annihilation as a complement-block combination whose coefficients are the
`c`-weighted blue coupling coefficients. Injectivity of the complement block removes
the complement part, leaving `c`-weighted blue coupling coefficients that vanish for
every complement boundary configuration. The blue coupling coefficient, read as a
function of the blue physical leg, factors through the blue block's blocked-region
weights; injectivity of the blue block then removes the remaining part, forcing
`c = 0`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `injective_union`, lines 1324--1400 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d} {e : Edge G}

/-! ### Viewing edge blocking data as a bare three-block geometry

The union lemma is proved once over a bare `ThreeBlockGeometry` (in
`TNLean.PEPS.RegionBlock.UnionInjectivityGeneral2`). The
`NormalEdgeBlockingData`-parametrized theorems of this file are reformulations
that view the edge-centred red, blue, and complement blocks as that geometry
via `NormalEdgeBlockingData.toThreeBlockGeometry`.

A boundary edge of the host `univ \ red` has one endpoint in `univ \ red` and one
in `red`. The host-side endpoint lies in the blue block or in the complement block
(the two cover `univ \ red`). When it lies in blue the edge is a boundary edge of
the blue block (the red endpoint is outside blue); when it lies in complement the
edge is a boundary edge of the complement block (the red endpoint is outside
complement). A host boundary configuration is therefore the data of a blue
boundary configuration on the blue/red crossing edges and a complement boundary
configuration on the complement/red crossing edges, recombined by
`ThreeBlockGeometry.hostLabelFrom`. -/

/-- View the one-edge blocking data as a bare three-block geometry: the same
red, blue, and complement blocks, keeping only their pairwise disjointness and
the cover of the vertex set, and forgetting the injectivity witnesses and the
distinguished edge. -/
def NormalEdgeBlockingData.toThreeBlockGeometry
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    ThreeBlockGeometry V where
  red := D.red
  blue := D.blue
  complement := D.complement
  red_disjoint_blue := D.red_disjoint_blue
  red_disjoint_complement := D.red_disjoint_complement
  blue_disjoint_complement := D.blue_disjoint_complement
  cover_univ := D.cover_univ

/-! ### The union of the blue and complement blocks is injective

Assembling the blue inversion, the complement coupling collapse, and the host boundary
surjectivity into the source's `injective_union` for the load-bearing instance: the
host block `univ \ red`, the union of the blue and complement blocks, is blocked-tensor
injective. -/

open scoped Classical in
/-- **The union lemma of the normal PEPS Fundamental Theorem.** The host block
`univ \ red`, the union of the blue and complement injective blocks of a
`NormalEdgeBlockingData`, is blocked-tensor injective.

A coefficient family `c` annihilating the host blocked-region weight family is stripped
of the blue block (`ThreeBlockGeometry.complCoeff_combination_eq_zero`), leaving the
`c`-weighted complement
coupling coefficients vanishing for every complement physical leg and blue boundary
configuration. The complement coupling collapse
(`ThreeBlockGeometry.blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq`) reads each as
a complement-blocked combination; injectivity of the complement block forces, for every
blue and complement boundary configuration realized by a global configuration, the host
residual coefficient reconstructed from them to vanish. Surjectivity of the host boundary
label (`ThreeBlockGeometry.exists_regionBoundaryLabel_host_eq`) makes every host residual
realized, so `c = 0`.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_union
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g) :
    RegionBlockedTensorInjective (G := G) A (Finset.univ \ D.red) :=
  D.toThreeBlockGeometry.regionBlockedTensorInjective_union
    (regionBlockedTensorInjective_blue (A := A) (e := e) D)
    (regionBlockedTensorInjective_complement (A := A) (e := e) D) hpos

/-- **The host block is blocked-tensor injective.** The set complement of the red block
of a `NormalEdgeBlockingData`, the union of the blue and complement blocks, is
blocked-tensor injective: the union lemma applied to the injectivity of the blue and
complement blocks individually.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_compl_red
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g) :
    RegionBlockedTensorInjective (G := G) A (Finset.univ \ D.red) :=
  regionBlockedTensorInjective_union (A := A) (e := e) D hpos

end PEPS
end TNLean
