/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NormalBlocking
import TNLean.PEPS.RegionBlock.UnionClosure
import TNLean.PEPS.TwoInjectiveComparison

/-!
# Region-two-block wrapping for the normal PEPS Fundamental Theorem

The normal PEPS proof of arXiv:1804.04964, Section 3 first blocks the lattice
into injective regions and then runs the *same* three-site injective-chain
argument used for injective PEPS. The one-edge datum of that blocking is a triple
of regions: a red region holding the left endpoint, a blue region holding the
right endpoint, and the complementary region; the three are pairwise disjoint,
cover the lattice, and are each injective (`NormalEdgeBlockingData`).

This file performs the region analogue of the vertex-two-block wrapping of
`TNLean.PEPS.FundamentalTheorem.OneVertexComparison`. There the selected vertex
and its complement are wrapped as abstract `TwoBlockTensor`s over the bonds
incident to the vertex; here a finite region is wrapped as a `TwoBlockTensor`
over the edges crossing its boundary, and its injectivity is exactly the linear
independence of the blocked-region tensor family.

The wrapped two-block tensors and their injectivity are the region-level input to
the abstract two-injective comparison
(`two_injective_tensor_insertion_comparison`,
`one_vertex_complement_comparison`) that the injective Fundamental Theorem uses
unchanged. These wrappers use the full boundary of a single region. A later
two-region comparison must either compare a region with its complement, or choose
the shared interface as the common boundary and keep the other boundary legs as
external indices.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Theorem 3
  and the theorem labelled `normal`, lines 1407--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### A finite region as an abstract two-block tensor

The blocked tensor of a region `R` carries open virtual legs on the edges
crossing the boundary of `R` and physical legs on the vertices of `R`. As an
abstract two-block tensor the crossing edges are the shared bonds, the external
boundary is a one-point space, and the region's physical configuration is the
physical leg. -/

/-- A finite region `R`, viewed as an abstract two-block tensor over the edges
crossing the boundary of `R`, with a one-point external boundary and the region
physical configuration as physical leg.

This is the region analogue of `vertexTwoBlock`: the role played there by the
single vertex and the bonds incident to it is played here by the whole region `R`
and the edges crossing its boundary.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`, where each blocked region is compared as
an injective block. -/
noncomputable def regionTwoBlock (A : Tensor G d) (R : Finset V) :
    TwoBlockTensor (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (fun f => Fin (A.bondDim f.1)) PUnit
      (RegionPhysicalConfig (V := V) (d := d) R) :=
  fun _ bdry τ => regionBlockedWeight (G := G) A R bdry τ

@[simp] theorem regionTwoBlock_apply (A : Tensor G d) (R : Finset V)
    (u : PUnit) (bdry : RegionBoundaryConfig (G := G) A R)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionTwoBlock (G := G) A R u bdry τ = regionBlockedWeight (G := G) A R bdry τ := rfl

/-- The region two-block tensor is two-block injective exactly when the
blocked-region tensor family of `R` is linearly independent.

The auxiliary one-point external boundary is absorbed by `Equiv.punitProd`,
turning the abstract joint-configuration linear independence of the two-block
tensor into the boundary-configuration linear independence of the blocked-region
tensor family, and conversely.

Source: arXiv:1804.04964, Section 3, lines 205--250 of
`Papers/1804.04964/paper_normal.tex`, where a contraction of injective tensors
over a region is injective. -/
theorem isTwoBlockInjective_regionTwoBlock_iff (A : Tensor G d) (R : Finset V) :
    IsTwoBlockInjective (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
        (bondDim := fun f => Fin (A.bondDim f.1)) (regionTwoBlock (G := G) A R) ↔
      RegionBlockedTensorInjective (G := G) A R := by
  unfold IsTwoBlockInjective RegionBlockedTensorInjective
  have hequiv :
      (fun η : PUnit × RegionBoundaryConfig (G := G) A R =>
          fun τ : RegionPhysicalConfig (V := V) (d := d) R =>
            regionTwoBlock (G := G) A R η.1 η.2 τ) =
        (regionBlockedTensorFamily (G := G) A R) ∘ (Equiv.punitProd _) := by
    funext η τ; rfl
  rw [hequiv]
  let eunit : PUnit × RegionBoundaryConfig (G := G) A R ≃
      RegionBoundaryConfig (G := G) A R := Equiv.punitProd _
  constructor
  · intro h
    have := h.comp eunit.symm eunit.symm.injective
    convert this using 1
    ext ρ τ
    simp [eunit, Function.comp]
  · intro h
    exact h.comp eunit eunit.injective

/-- The region two-block tensor is two-block injective whenever the blocked-region
tensor family of `R` is linearly independent.

Source: arXiv:1804.04964, Section 3, lines 205--250 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTwoBlockInjective_regionTwoBlock (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R) :
    IsTwoBlockInjective (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (bondDim := fun f => Fin (A.bondDim f.1)) (regionTwoBlock (G := G) A R) :=
  (isTwoBlockInjective_regionTwoBlock_iff (G := G) A R).mpr hR

end PEPS
end TNLean
