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
via `NormalEdgeBlockingData.toThreeBlockGeometry`. -/

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

/-! ### Reconstructing a host boundary configuration from blue and complement data

A boundary edge of the host `univ \ red` has one endpoint in `univ \ red` and one in
`red`. The host-side endpoint lies in the blue block or in the complement block (the
two cover `univ \ red`). When it lies in blue the edge is a boundary edge of the blue
block (the red endpoint is outside blue); when it lies in complement the edge is a
boundary edge of the complement block (the red endpoint is outside complement). A host
boundary configuration is therefore the data of a blue boundary configuration on the
blue/red crossing edges and a complement boundary configuration on the complement/red
crossing edges, recombined by `ThreeBlockGeometry.hostLabelFrom`. -/

/-! ### The blue inversion of the host annihilation

A coefficient family `c` annihilating the blocked-region weight family of the host
`univ \ red` annihilates, at every fused blue/complement physical leg, the host
weight. Reading the resulting identity as a function of the blue physical leg and
applying the blue block's chosen left inverse strips the blue block, leaving the
`c`-weighted complement coupling coefficients vanishing for every complement physical
leg and blue boundary configuration. -/

open scoped Classical in
/-- The blue block strips out of the host annihilation. If the coefficient family `c`
annihilates the blocked-region weight family of the host `univ \ red`, then for every
complement physical leg `σcompl` and blue boundary configuration `bβ`, the
`c`-weighted sum of complement coupling coefficients
`threeBlockComplCoeff D bdry σcompl bβ` vanishes.

The annihilation, evaluated at the fused leg `threeBlockComplPhysical D σblue σcompl`,
holds for every blue leg `σblue`. Scaling by the nonzero blue interior bond product
and applying the blue scalar-multiplication factorization
(`regionInteriorBondProd_smul_threeBlockBlueWeight_eq`) rewrites the host weights as
the complement-coupling combination of the blue blocked-region weights; the blue
block's chosen left inverse then reads off the complement coupling row.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem complCoeff_combination_eq_zero
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (c : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red) → ℂ)
    (hc : ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
        c bdry • regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry = 0)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (bβ : RegionBoundaryConfig (G := G) A D.blue) :
    ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
        c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ = 0 :=
  D.toThreeBlockGeometry.complCoeff_combination_eq_zero
    (regionBlockedTensorInjective_blue (A := A) (e := e) D) c hc σcompl bβ

/-! ### The blue/red crossing multiplicity collapse of the complement coupling

The complement coupling coefficient `threeBlockComplCoeff D bdry σcompl bβ`, read as a
function of the complement physical leg `σcompl`, lies in the range of the complement
block's blocked-region tensor map, with the coefficient row supported on the single
host residual `bdry` reconstructed from `bβ` and the complement boundary configuration.

The route mirrors `stateCoeff_eq_regionComplement` at the level of the constrained
coupling sum. Grouping the global configurations of `threeBlockComplCoeff` by the
complement boundary configuration `bc'` they induce, each inner sum runs over the
configurations carrying the three prescribed boundary labels (host `bdry`, blue `bβ`,
complement `bc'`). The complement blocked-region weight at `bc'` runs over the larger
family of configurations carrying only the complement label `bc'`; the difference is
the free virtual indices on the red/blue crossing edges, which the complement vertex
product ignores. Projecting away those crossing indices collapses the larger sum onto
the constrained sum with the red/blue crossing bond product as the constant fiber
multiplicity. When no configuration carries the three labels (the host residual is not
the one reconstructed from `bβ` and `bc'`, or `bβ` and `bc'` clash on a blue/complement
crossing edge) the constrained sum is empty and the collapse is the zero identity. -/

/-- The red/blue crossing edges: the boundary edges of the red block that are also
boundary edges of the blue block. These are the free virtual indices distinguishing the
complement blocked-region weight from the constrained complement coupling sum. -/
def IsBlueRedCrossingEdge
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) (g : Edge G) :
    Prop :=
  IsRegionBoundaryEdge (G := G) D.red g ∧ IsRegionBoundaryEdge (G := G) D.blue g

instance
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) (g : Edge G) :
    Decidable (IsBlueRedCrossingEdge (A := A) (e := e) D g) := by
  unfold IsBlueRedCrossingEdge; infer_instance

/-- The bond-dimension product over the red/blue crossing edges: the constant fiber
multiplicity of the complement coupling collapse. -/
noncomputable def blueRedCrossingBondProd
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) : ℕ :=
  ∏ g ∈ Finset.univ.filter (fun g : Edge G => IsBlueRedCrossingEdge (A := A) (e := e) D g),
    A.bondDim g

open scoped Classical in
/-- **The per-fiber complement weight collapse.** When some global configuration `q₀`
carries the three boundary labels (host `bdry`, blue `bβ`, complement `bc'`), the
complement blocked-region weight at `bc'` is the red/blue crossing bond product times
the constrained complement coupling sum over the configurations carrying the three
labels. Grouping the complement-labelled configurations by overwriting their red/blue
crossing indices with those of `q₀`, the complement vertex product is constant on each
fiber and each fiber has cardinality the red/blue crossing bond product. -/
theorem regionBlockedWeight_complement_eq_smul_constrained
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (bβ : RegionBoundaryConfig (G := G) A D.blue)
    (bc' : RegionBoundaryConfig (G := G) A D.complement)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (q₀ : VirtualConfig A)
    (hq0host : regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q₀ = bdry)
    (hq0blue : regionBoundaryLabel (G := G) A D.blue q₀ = bβ)
    (hq0compl : regionBoundaryLabel (G := G) A D.complement q₀ = bc') :
    regionBlockedWeight (G := G) A D.complement bc' σcompl =
      blueRedCrossingBondProd (A := A) (e := e) D •
        ∑ q ∈ Finset.univ.filter
            (fun q : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
                regionBoundaryLabel (G := G) A D.blue q = bβ ∧
                  regionBoundaryLabel (G := G) A D.complement q = bc'),
          ∏ w : {w : V // w ∈ D.complement},
            A.component w.1 (fun ie => q ie.1) (σcompl w) :=
  D.toThreeBlockGeometry.regionBlockedWeight_complement_eq_smul_constrained
    bdry bβ bc' σcompl q₀ hq0host hq0blue hq0compl

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
of the blue block (`complCoeff_combination_eq_zero`), leaving the `c`-weighted complement
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
    (_hblue : RegionBlockedTensorInjective (G := G) A D.blue)
    (_hcompl : RegionBlockedTensorInjective (G := G) A D.complement)
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
  regionBlockedTensorInjective_union (A := A) (e := e) D
    (regionBlockedTensorInjective_blue (A := A) (e := e) D)
    (regionBlockedTensorInjective_complement (A := A) (e := e) D) hpos

end PEPS
end TNLean
