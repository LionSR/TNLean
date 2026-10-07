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
blue-side fiber-collapse factorization over a bare `ThreeBlockGeometry`: the pointwise
capstone
`regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue` and its
function-level form `regionInteriorBondProd_smul_geometryBlueWeight_eq`, the
factorization the two-step inverse application of Lemma `injective_union`
(arXiv:1804.04964, Section 3, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`) consumes.

## Implementation notes

The blue-side results are obtained from the complement-side results by interchanging
the blue and complement blocks of `ThreeBlockGeometry`. The operation
`ThreeBlockGeometry.swapBlueComplement` records this mathematical symmetry once; its
reducible projections let later coupling identities unfold to the corresponding
blue/complement formulas.

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

This geometry involution, rather than square-lattice coordinate swap, is the exact
symmetry of the declarations below: they hold for an arbitrary graph and exchange two
configuration fibers, not two coordinate axes. -/
abbrev ThreeBlockGeometry.swapBlueComplement (g : ThreeBlockGeometry V) :
    ThreeBlockGeometry V where
  red := g.red
  blue := g.complement
  complement := g.blue
  red_disjoint_blue := g.red_disjoint_complement
  red_disjoint_complement := g.red_disjoint_blue
  blue_disjoint_complement := g.blue_disjoint_complement.symm
  cover_univ := by rw [← g.cover_univ]; ac_rfl

omit [LinearOrder V] in
/-- Swapping the blue and complement blocks leaves the red block unchanged. -/
@[simp] theorem ThreeBlockGeometry.swapBlueComplement_red :
    g.swapBlueComplement.red = g.red := rfl

omit [LinearOrder V] in
/-- The blue block after swapping is the original complement block. -/
@[simp] theorem ThreeBlockGeometry.swapBlueComplement_blue :
    g.swapBlueComplement.blue = g.complement := rfl

omit [LinearOrder V] in
/-- The complement block after swapping is the original blue block. -/
@[simp] theorem ThreeBlockGeometry.swapBlueComplement_complement :
    g.swapBlueComplement.complement = g.blue := rfl

omit [LinearOrder V] in
/-- The physical configuration on the swapped complement agrees with the original fused
configuration after interchanging the blue and complement arguments. -/
@[simp] theorem ThreeBlockGeometry.swapBlueComplement_complPhysical
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    g.swapBlueComplement.complPhysical σcompl σblue =
      g.complPhysical σblue σcompl := by
  funext w
  by_cases hb : w.1 ∈ g.blue
  · have hc : w.1 ∉ g.complement := fun hw ↦
      (Finset.disjoint_left.mp g.blue_disjoint_complement) hb hw
    simp [ThreeBlockGeometry.complPhysical, swapBlueComplement, hb, hc]
  · have hc : w.1 ∈ g.complement := by
      have hbc : w.1 ∈ g.blue ∪ g.complement := by
        rw [← g.sdiff_red_eq_blue_union_complement]
        exact w.2
      exact (Finset.mem_union.mp hbc).resolve_left hb
    simp [ThreeBlockGeometry.complPhysical, swapBlueComplement, hb, hc]

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
  g.swapBlueComplement.threeBlockBlueCoeff bdry σcompl bβ

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
  rw [← g.swapBlueComplement_complPhysical σblue σcompl]
  exact
    ThreeBlockGeometry.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical
      g.swapBlueComplement bdry σcompl σblue

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
  funext σblue
  rw [Pi.smul_apply, Finset.sum_apply,
    g.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue
      bdry σblue σcompl]
  refine Finset.sum_congr rfl (fun bβ _ => ?_)
  rw [Pi.smul_apply]

end PEPS
end TNLean
