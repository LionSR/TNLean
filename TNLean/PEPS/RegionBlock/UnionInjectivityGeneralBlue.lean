/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral
import TNLean.PEPS.ConfigurationCalculus

/-!
# The general union lemma: the blue-side fiber-collapse factorization

This file continues `TNLean.PEPS.RegionBlock.UnionInjectivityGeneral` with the
blue-side mirror of the complement-side fiber-collapse factorization, over a bare
`ThreeBlockGeometry`. Together with that file it supplies both factorizations the
two-step inverse application of Lemma `injective_union` (arXiv:1804.04964, Section 3,
lines 1324--1400 of `Papers/1804.04964/paper_normal.tex`) consumes.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `injective_union`, lines 1324--1400 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}
variable (g : ThreeBlockGeometry V)

/-- Exchange the blue and complement roles while leaving the red block fixed.

This local geometry involution, rather than square-lattice coordinate swap, is the exact
symmetry of the declarations below: they hold for an arbitrary graph and exchange two
configuration fibers, not two coordinate axes. -/
private def ThreeBlockGeometry.swapBlueComplementMirror (g : ThreeBlockGeometry V) :
    ThreeBlockGeometry V where
  red := g.red
  blue := g.complement
  complement := g.blue
  red_disjoint_blue := g.red_disjoint_complement
  red_disjoint_complement := g.red_disjoint_blue
  blue_disjoint_complement := g.blue_disjoint_complement.symm
  cover_univ := by rw [← g.cover_univ]; ac_rfl

omit [LinearOrder V] in
@[simp] private theorem ThreeBlockGeometry.swapBlueComplementMirror_complPhysical
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    g.swapBlueComplementMirror.complPhysical σcompl σblue =
      g.complPhysical σblue σcompl := by
  funext w
  by_cases hb : w.1 ∈ g.blue
  · have hc : w.1 ∉ g.complement := fun hw ↦
      (Finset.disjoint_left.mp g.blue_disjoint_complement) hb hw
    simp [ThreeBlockGeometry.complPhysical, swapBlueComplementMirror, hb, hc]
  · have hc : w.1 ∈ g.complement := by
      have hbc : w.1 ∈ g.blue ∪ g.complement := by
        rw [← g.sdiff_red_eq_blue_union_complement]
        exact w.2
      exact (Finset.mem_union.mp hbc).resolve_left hb
    simp [ThreeBlockGeometry.complPhysical, swapBlueComplementMirror, hb, hc]

/-- The complement vertex product reads a global configuration only through the
complement-incident edges, so it agrees with the configuration merged along the blue
block, provided the two configurations agree on the blue boundary. This is the blue
mirror of `blueProd_eq_regionMerge_complement`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.complProd_eq_regionMerge_blue
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A g.blue p.1 =
      regionBoundaryLabel (G := G) A g.blue p.2) :
    (∏ w : {w : V // w ∈ g.complement}, A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      ∏ w : {w : V // w ∈ g.complement},
        A.component w.1 (fun ie => regionMerge (G := G) A g.blue p ie.1) (σcompl w) := by
  simpa [swapBlueComplementMirror] using
    g.swapBlueComplementMirror.blueProd_eq_regionMerge_complement σcompl p hp

/-- On a boundary edge of the host `univ \ red`, the complement-side configuration
`p.2` agrees with the configuration merged along the blue block, provided the pair
agrees on the blue boundary. This is the blue mirror of
`hostLabel_p2_eq_hostLabel_regionMerge_complement`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.hostLabel_p2_eq_hostLabel_regionMerge_blue
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A g.blue p.1 =
      regionBoundaryLabel (G := G) A g.blue p.2) :
    regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 =
      regionBoundaryLabel (G := G) A (Finset.univ \ g.red)
        (regionMerge (G := G) A g.blue p) := by
  simpa [swapBlueComplementMirror] using
    g.swapBlueComplementMirror.hostLabel_p2_eq_hostLabel_regionMerge_complement p hp
open scoped Classical in
/-- **The host-relative blue fiber cardinality.** The blue mirror of
`threeBlockFiber_card`: among the blue-boundary-agreeing pairs whose complement-side
host label is `bdry`, the fiber over a blue merge `η` has cardinality the blue
interior bond product when `η` has host label `bdry`, and is empty otherwise.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.threeBlockBlueFiber_card
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (η : VirtualConfig A) :
    (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
          (regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2 ∧
            regionMerge (G := G) A g.blue p = η))).card =
      if regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry then
        regionInteriorBondProd (G := G) A g.blue else 0 := by
  simpa [swapBlueComplementMirror] using
    g.swapBlueComplementMirror.threeBlockFiber_card bdry η

open scoped Classical in
/-- **The host-relative blue merge collapse.** The blue mirror of
`threeBlockDoubleSum_eq_smul_single`: the blue-boundary-agreeing double sum of the
blue vertex product against the complement vertex product, with the complement side
constrained to host label `bdry`, collapses to the blue interior bond product times
the single constrained sum.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.threeBlockDoubleSum_eq_smul_single_blue
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2),
      (∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      regionInteriorBondProd (G := G) A g.blue •
        ∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ g.red) ζ = bdry),
          (∏ w : {w : V // w ∈ g.blue},
              A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
            ∏ w : {w : V // w ∈ g.complement},
              A.component w.1 (fun ie => ζ ie.1) (σcompl w) := by
  simpa [swapBlueComplementMirror] using
    g.swapBlueComplementMirror.threeBlockDoubleSum_eq_smul_single bdry σcompl σblue

open scoped Classical in
/-- **The complement coupling coefficient.** The blue mirror of
`threeBlockBlueCoeff`: the complement vertex product summed over all global
configurations whose host label is `bdry` and whose blue boundary label is the
prescribed `bβ`. This is the complement-block contraction coupled to the blue
boundary configuration through the blue/complement crossing bonds.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def ThreeBlockGeometry.threeBlockComplCoeff
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (bβ : RegionBoundaryConfig (G := G) A g.blue) : ℂ :=
  g.swapBlueComplementMirror.threeBlockBlueCoeff bdry σcompl bβ

open scoped Classical in
/-- **The host-relative blue decoupling.** The blue mirror of
`threeBlockDoubleSum_eq_blueCoeff_sum`: the blue-boundary-agreeing double sum of the
blue vertex product against the host-constrained complement vertex product decouples,
grouped by the blue boundary configuration `bβ`, into the blue blocked-region weight
at `bβ` against the complement coupling coefficient.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.threeBlockDoubleSum_eq_complCoeff_sum_blue
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2),
      (∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      ∑ bβ : RegionBoundaryConfig (G := G) A g.blue,
        regionBlockedWeight (G := G) A g.blue bβ σblue *
          g.threeBlockComplCoeff bdry σcompl bβ := by
  simpa [swapBlueComplementMirror, threeBlockComplCoeff] using
    g.swapBlueComplementMirror.threeBlockDoubleSum_eq_blueCoeff_sum bdry σcompl σblue

namespace ThreeBlockGeometry

open scoped Classical in
/-- **The core blue smul-factorization (pointwise).** The blue mirror of
`regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical`: the blue
interior bond multiple of the fused host weight, at a fixed blue physical leg, is the
sum over blue boundary configurations of the complement coupling coefficient times
the blue blocked-region weight.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (regionInteriorBondProd (G := G) A g.blue : ℂ) •
        regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
          (g.complPhysical σblue σcompl) =
      ∑ bβ : RegionBoundaryConfig (G := G) A g.blue,
        g.threeBlockComplCoeff bdry σcompl bβ •
          regionBlockedWeight (G := G) A g.blue bβ σblue := by
  simpa [swapBlueComplementMirror, threeBlockComplCoeff] using
    g.swapBlueComplementMirror.
      regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical
        bdry σcompl σblue

end ThreeBlockGeometry

open scoped Classical in
/-- **The core blue smul-factorization (as functions of `σblue`).** The blue
interior bond multiple of the fused host weight, read as a function of the blue
physical leg, is the complement-coupling combination of the blue blocked-region
weights.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_geometryBlueWeight_eq
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (regionInteriorBondProd (G := G) A g.blue : ℂ) •
        (fun σblue : RegionPhysicalConfig (V := V) (d := d) g.blue =>
          regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
            (g.complPhysical σblue σcompl)) =
      ∑ bβ : RegionBoundaryConfig (G := G) A g.blue,
        g.threeBlockComplCoeff bdry σcompl bβ •
          regionBlockedWeight (G := G) A g.blue bβ := by
  simpa [swapBlueComplementMirror, threeBlockComplCoeff] using
    g.swapBlueComplementMirror.regionInteriorBondProd_smul_threeBlockComplWeight_eq
      bdry σcompl

end PEPS
end TNLean
