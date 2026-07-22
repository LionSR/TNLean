/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionTransportData
import TNLean.PEPS.SquareLatticeGraph
import TNLean.PEPS.NormalEdgeBlockingTranslated

/-!
# Coordinate swap on finite square lattices

Interchanging the two coordinates identifies the `width × height` square lattice
with the `height × width` lattice. This exchanges horizontal and vertical edges
and transposes contiguous rectangles.
-/

namespace TNLean
namespace PEPS

/-- Interchange the coordinates of a finite square-lattice vertex. -/
def squareLatticeCoordinateSwapEquiv (width height : ℕ) :
    SquareLatticeVertex width height ≃ SquareLatticeVertex height width :=
  Equiv.prodComm (Fin width) (Fin height)

@[simp] theorem squareLatticeCoordinateSwapEquiv_apply {width height : ℕ}
    (v : SquareLatticeVertex width height) :
    squareLatticeCoordinateSwapEquiv width height v = (v.2, v.1) :=
  rfl

/-- Coordinate swap exchanges horizontal and vertical square-lattice neighbours. -/
theorem squareLatticeHorizontalNeighbor_coordinateSwap {width height : ℕ}
    {v w : SquareLatticeVertex width height} :
    squareLatticeVerticalNeighbor (squareLatticeCoordinateSwapEquiv width height v)
      (squareLatticeCoordinateSwapEquiv width height w) ↔
      squareLatticeHorizontalNeighbor v w :=
  Iff.rfl

/-- Coordinate swap exchanges vertical and horizontal square-lattice neighbours. -/
theorem squareLatticeVerticalNeighbor_coordinateSwap {width height : ℕ}
    {v w : SquareLatticeVertex width height} :
    squareLatticeHorizontalNeighbor (squareLatticeCoordinateSwapEquiv width height v)
      (squareLatticeCoordinateSwapEquiv width height w) ↔
        squareLatticeVerticalNeighbor v w :=
  Iff.rfl

/-- Coordinate swap as an isomorphism of finite square-lattice graphs. -/
def squareLatticeCoordinateSwap {width height : ℕ} :
    squareLatticeGraph width height ≃g squareLatticeGraph height width where
  toEquiv := squareLatticeCoordinateSwapEquiv width height
  map_rel_iff' := by
    intro v w
    rw [squareLatticeGraph_adj, squareLatticeGraph_adj]
    rw [squareLatticeHorizontalNeighbor_coordinateSwap,
      squareLatticeVerticalNeighbor_coordinateSwap, or_comm]

@[simp] theorem squareLatticeCoordinateSwap_apply {width height : ℕ}
    (v : SquareLatticeVertex width height) :
    squareLatticeCoordinateSwap v = (v.2, v.1) :=
  rfl

@[simp] theorem squareLatticeCoordinateSwap_symm {width height : ℕ} :
    (squareLatticeCoordinateSwap (width := width) (height := height)).symm =
      squareLatticeCoordinateSwap (width := height) (height := width) :=
  rfl

@[simp] theorem Edge.map_squareLatticeCoordinateSwap_map {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) :
    Edge.map (squareLatticeCoordinateSwap (width := height) (height := width))
        (Edge.map squareLatticeCoordinateSwap e) = e := by
  rw [← squareLatticeCoordinateSwap_symm]
  exact Edge.map_symm_map squareLatticeCoordinateSwap e

/-- Coordinate swap transposes a contiguous square-lattice rectangle. -/
theorem Region_map_squareLatticeCoordinateSwap_contiguousRectangle
    {width height : ℕ} (xStart yStart xLength yLength : ℕ) :
    Region.map squareLatticeCoordinateSwap
        (squareLatticeContiguousRectangle xStart yStart xLength yLength) =
      (squareLatticeContiguousRectangle yStart xStart yLength xLength :
        Finset (SquareLatticeVertex height width)) := by
  ext v
  simp only [mem_Region_map, squareLatticeCoordinateSwap_symm,
    squareLatticeCoordinateSwap_apply, mem_squareLatticeContiguousRectangle]
  tauto

/-- Injectivity of a region for a coordinate-swapped tensor is injectivity of its
transposed preimage for the original tensor. -/
theorem regionInjectivityDataOf_transport_squareLatticeCoordinateSwap_isInjective
    {width height d : ℕ} (A : Tensor (squareLatticeGraph width height) d)
    (R : Finset (SquareLatticeVertex height width)) :
    (regionInjectivityDataOf (A.transport squareLatticeCoordinateSwap)).IsInjective R ↔
      (regionInjectivityDataOf A).IsInjective
        (Region.map (squareLatticeCoordinateSwap (width := height) (height := width)) R) := by
  change RegionBlockedTensorInjective (A.transport squareLatticeCoordinateSwap) R ↔
    RegionBlockedTensorInjective A (Region.map squareLatticeCoordinateSwap R)
  let S := Region.map
    (squareLatticeCoordinateSwap (width := height) (height := width)) R
  have hS : Region.map
      (squareLatticeCoordinateSwap (width := width) (height := height)) S = R := by
    ext v
    simp only [S, mem_Region_map, squareLatticeCoordinateSwap_symm,
      squareLatticeCoordinateSwap_apply]
  change RegionBlockedTensorInjective (A.transport squareLatticeCoordinateSwap) R ↔
    RegionBlockedTensorInjective A S
  rw [← hS]
  exact regionBlockedTensorInjective_transport A squareLatticeCoordinateSwap S

/-- Coordinate swap preserves the rectangular injectivity hypotheses of a tensor. -/
theorem NormalSquareLatticeRectangleInjectivityHypotheses.transportCoordinateSwap
    {width height d : ℕ} (A : Tensor (squareLatticeGraph width height) d)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses (regionInjectivityDataOf A)) :
    NormalSquareLatticeRectangleInjectivityHypotheses
      (regionInjectivityDataOf (A.transport squareLatticeCoordinateSwap)) where
  twoByThree_injective := by
    rintro R ⟨x, y, hx, hy, rfl⟩
    rw [regionInjectivityDataOf_transport_squareLatticeCoordinateSwap_isInjective,
      Region_map_squareLatticeCoordinateSwap_contiguousRectangle]
    exact h.rect32_injective hy hx
  threeByTwo_injective := by
    rintro R ⟨x, y, hx, hy, rfl⟩
    rw [regionInjectivityDataOf_transport_squareLatticeCoordinateSwap_isInjective,
      Region_map_squareLatticeCoordinateSwap_contiguousRectangle]
    exact h.rect23_injective hy hx

/-- Coordinate swap preserves closure of tensor injectivity under unions. -/
theorem RegionInjectivityUnionClosure.transportCoordinateSwap
    {width height d : ℕ} (A : Tensor (squareLatticeGraph width height) d)
    (h : RegionInjectivityUnionClosure (regionInjectivityDataOf A)) :
    RegionInjectivityUnionClosure
      (regionInjectivityDataOf (A.transport squareLatticeCoordinateSwap)) where
  union_injective := by
    intro R S hR hS
    rw [regionInjectivityDataOf_transport_squareLatticeCoordinateSwap_isInjective] at hR hS ⊢
    rw [Region_map_union]
    exact h.union_injective hR hS

/-- Coordinate swap sends the red block of a translated vertical edge to the red block of the
transposed horizontal edge. -/
theorem Region_map_squareLatticeCoordinateSwap_verticalTranslatedEdgeRed
    {width height xStart yStart : ℕ} :
    Region.map squareLatticeCoordinateSwap
        (normalSquareVerticalTranslatedEdgeRed xStart yStart) =
      (normalSquareHorizontalTranslatedEdgeRed yStart xStart :
        Finset (SquareLatticeVertex height width)) := by
  simpa only [normalSquareVerticalTranslatedEdgeRed,
    normalSquareHorizontalTranslatedEdgeRed, normalSquareRegionTVerticalBlock] using
    Region_map_squareLatticeCoordinateSwap_contiguousRectangle
      (width := width) (height := height) (xStart + 2) yStart 3 2

/-- Coordinate swap sends the blue block of a translated vertical edge to the blue block of the
transposed horizontal edge. -/
theorem Region_map_squareLatticeCoordinateSwap_verticalTranslatedEdgeBlue
    {width height xStart yStart : ℕ} :
    Region.map squareLatticeCoordinateSwap
        (normalSquareVerticalTranslatedEdgeBlue xStart yStart) =
      (normalSquareHorizontalTranslatedEdgeBlue yStart xStart :
        Finset (SquareLatticeVertex height width)) := by
  simpa only [normalSquareVerticalTranslatedEdgeBlue,
    normalSquareHorizontalTranslatedEdgeBlue, normalSquareRegionTHorizontalBlock] using
    Region_map_squareLatticeCoordinateSwap_contiguousRectangle
      (width := width) (height := height) (xStart + 1) (yStart + 2) 2 3

/-- Coordinate swap sends the distinguished translated vertical edge to the
translated horizontal edge in the transposed frame. -/
theorem Edge.map_squareLatticeCoordinateSwap_verticalTranslatedEdge
    {width height xStart yStart : ℕ}
    (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    Edge.map squareLatticeCoordinateSwap
        (normalSquareVerticalTranslatedEdge xStart yStart hx hy) =
      normalSquareHorizontalTranslatedEdge yStart xStart hy hx := by
  apply Edge.ofAdj_eq_of_endpoints
  rcases Edge.map_endpoints squareLatticeCoordinateSwap
      (normalSquareVerticalTranslatedEdge xStart yStart hx hy) with h | h
  · exact Or.inl ⟨rfl, rfl⟩
  · exfalso
    have hlt := (Edge.map squareLatticeCoordinateSwap
      (normalSquareVerticalTranslatedEdge xStart yStart hx hy)).2.1
    rw [h.1, h.2] at hlt
    change toLex
      ((⟨yStart + 2, by omega⟩ : Fin height), (⟨xStart + 2, by omega⟩ : Fin width)) <
      toLex ((⟨yStart + 1, by omega⟩ : Fin height),
        (⟨xStart + 2, by omega⟩ : Fin width)) at hlt
    rw [Prod.Lex.toLex_lt_toLex] at hlt
    simp at hlt

end PEPS
end TNLean
