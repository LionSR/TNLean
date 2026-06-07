import TNLean.PEPS.NormalBlocking
import TNLean.PEPS.RegionBlock.UnionClosure
import TNLean.PEPS.TwoInjectiveComparison
import TNLean.PEPS.FundamentalTheorem.OneVertexComparison

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
incident to the vertex; here the red, blue, and complementary regions are wrapped
as `TwoBlockTensor`s over the edges crossing each region's boundary, and their
injectivity is read off the concrete region-injectivity predicate
`regionInjectivityDataOf A` of Phases A--B.

For a vertex-injective PEPS with positive bond dimensions, the concrete predicate
`regionInjectivityDataOf A` makes *every* finite region injective
(`regionBlockedTensorInjective_of_isVertexInjective`); under that instantiation
the abstract region-injectivity facts of the normal blocking hypotheses become
the concrete linear independence of the blocked-region tensor families, which is
exactly two-block injectivity of the wrapped regions.

The wrapped two-block tensors and their injectivity are the region-level input to
the abstract two-injective comparison
(`two_injective_tensor_insertion_comparison`,
`one_vertex_complement_comparison`) that the injective Fundamental Theorem uses
unchanged. The remaining step toward the per-edge gauge is recorded at the end of
this file.

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
  constructor
  · intro h
    have := h.comp (Equiv.punitProd _).symm (Equiv.punitProd _).symm.injective
    simpa [Function.comp] using this
  · intro h
    exact h.comp _ (Equiv.punitProd _).injective

/-- The region two-block tensor is two-block injective whenever the blocked-region
tensor family of `R` is linearly independent.

Source: arXiv:1804.04964, Section 3, lines 205--250 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTwoBlockInjective_regionTwoBlock (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R) :
    IsTwoBlockInjective (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (bondDim := fun f => Fin (A.bondDim f.1)) (regionTwoBlock (G := G) A R) :=
  (isTwoBlockInjective_regionTwoBlock_iff (G := G) A R).mpr hR

/-- For a vertex-injective PEPS with positive bond dimensions, the region
two-block tensor of *every* finite region is two-block injective.

This is the concrete instantiation of the abstract region-injectivity predicate
`regionInjectivityDataOf A` at the wrapped two-block tensor: Phase A's
kernel-descent result makes every region injective, which is exactly two-block
injectivity of the region two-block tensor.

Source: arXiv:1804.04964, Section 3, lines 205--250 and 1322--1404 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTwoBlockInjective_regionTwoBlock_of_isVertexInjective (A : Tensor G d)
    (hA : IsVertexInjective A) (hpos : ∀ e : Edge G, 0 < A.bondDim e) (R : Finset V) :
    IsTwoBlockInjective (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (bondDim := fun f => Fin (A.bondDim f.1)) (regionTwoBlock (G := G) A R) :=
  isTwoBlockInjective_regionTwoBlock (G := G) A R
    (regionBlockedTensorInjective_of_isVertexInjective (G := G) A R hA hpos)

/-! ### The three edge-centred regions as two-block tensors

At each edge the normal blocking supplies a red region containing the left
endpoint, a blue region containing the right endpoint, and the complementary
region. Each is wrapped as a region two-block tensor and is two-block injective
under the concrete region-injectivity predicate of a vertex-injective PEPS. -/

namespace NormalPEPSBlockingHypotheses

/-- The red edge-block of the normal blocking, wrapped as a region two-block
tensor.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def redTwoBlock [DecidableEq V] (A : Tensor G d)
    (h : NormalPEPSBlockingHypotheses (regionInjectivityDataOf (G := G) A) G) (e : Edge G) :
    TwoBlockTensor
      (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) (h.edgeBlocking.red e) f})
      (fun f => Fin (A.bondDim f.1)) PUnit
      (RegionPhysicalConfig (V := V) (d := d) (h.edgeBlocking.red e)) :=
  regionTwoBlock (G := G) A (h.edgeBlocking.red e)

/-- The blue edge-block of the normal blocking, wrapped as a region two-block
tensor.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def blueTwoBlock [DecidableEq V] (A : Tensor G d)
    (h : NormalPEPSBlockingHypotheses (regionInjectivityDataOf (G := G) A) G) (e : Edge G) :
    TwoBlockTensor
      (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) (h.edgeBlocking.blue e) f})
      (fun f => Fin (A.bondDim f.1)) PUnit
      (RegionPhysicalConfig (V := V) (d := d) (h.edgeBlocking.blue e)) :=
  regionTwoBlock (G := G) A (h.edgeBlocking.blue e)

/-- The complementary edge-block of the normal blocking, wrapped as a region
two-block tensor.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def complementTwoBlock [DecidableEq V] (A : Tensor G d)
    (h : NormalPEPSBlockingHypotheses (regionInjectivityDataOf (G := G) A) G) (e : Edge G) :
    TwoBlockTensor
      (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) (h.edgeBlocking.complement e) f})
      (fun f => Fin (A.bondDim f.1)) PUnit
      (RegionPhysicalConfig (V := V) (d := d) (h.edgeBlocking.complement e)) :=
  regionTwoBlock (G := G) A (h.edgeBlocking.complement e)

/-- The red region two-block tensor at each edge is two-block injective.

This reads the abstract injectivity of the red region supplied by the normal
blocking hypotheses (`injective_chain_at_edge`) as the concrete linear
independence of the red region's blocked tensor family, and wraps it as two-block
injectivity.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTwoBlockInjective_redTwoBlock [DecidableEq V] (A : Tensor G d)
    (h : NormalPEPSBlockingHypotheses (regionInjectivityDataOf (G := G) A) G) (e : Edge G) :
    IsTwoBlockInjective
      (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) (h.edgeBlocking.red e) f})
      (bondDim := fun f => Fin (A.bondDim f.1)) (redTwoBlock (G := G) A h e) :=
  isTwoBlockInjective_regionTwoBlock (G := G) A (h.edgeBlocking.red e)
    (h.injective_chain_at_edge e).1

/-- The blue region two-block tensor at each edge is two-block injective.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTwoBlockInjective_blueTwoBlock [DecidableEq V] (A : Tensor G d)
    (h : NormalPEPSBlockingHypotheses (regionInjectivityDataOf (G := G) A) G) (e : Edge G) :
    IsTwoBlockInjective
      (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) (h.edgeBlocking.blue e) f})
      (bondDim := fun f => Fin (A.bondDim f.1)) (blueTwoBlock (G := G) A h e) :=
  isTwoBlockInjective_regionTwoBlock (G := G) A (h.edgeBlocking.blue e)
    (h.injective_chain_at_edge e).2.1

/-- The complementary region two-block tensor at each edge is two-block injective.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTwoBlockInjective_complementTwoBlock [DecidableEq V] (A : Tensor G d)
    (h : NormalPEPSBlockingHypotheses (regionInjectivityDataOf (G := G) A) G) (e : Edge G) :
    IsTwoBlockInjective
      (Bond := {f : Edge G // IsRegionBoundaryEdge (G := G) (h.edgeBlocking.complement e) f})
      (bondDim := fun f => Fin (A.bondDim f.1)) (complementTwoBlock (G := G) A h e) :=
  isTwoBlockInjective_regionTwoBlock (G := G) A (h.edgeBlocking.complement e)
    (h.injective_chain_at_edge e).2.2

end NormalPEPSBlockingHypotheses

end PEPS
end TNLean
