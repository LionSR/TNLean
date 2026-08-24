/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionTransport
import TNLean.PEPS.TorusRectangleRegion

/-!
# Coordinate swap on the discrete torus

Interchanging the two coordinates identifies the `width × height` torus with the
`height × width` torus. This file records the graph isomorphism and the covariance
of finite regions and coordinate rectangles under that isomorphism. These lemmas let
proofs for horizontal regions be reused for their vertical transposes.
-/

namespace TNLean
namespace PEPS

/-- Interchange the two coordinates of a torus vertex. -/
def torusCoordinateSwapEquiv (width height : ℕ) :
    TorusVertex width height ≃ TorusVertex height width :=
  Equiv.prodComm (ZMod width) (ZMod height)

@[simp] theorem torusCoordinateSwapEquiv_apply {width height : ℕ}
    (v : TorusVertex width height) :
    torusCoordinateSwapEquiv width height v = (v.2, v.1) :=
  rfl

@[simp] theorem torusCoordinateSwapEquiv_symm {width height : ℕ} :
    (torusCoordinateSwapEquiv width height).symm = torusCoordinateSwapEquiv height width :=
  rfl

/-- Coordinate swap exchanges horizontal and vertical cyclic neighbours. -/
theorem torusHorizontalNeighbor_coordinateSwap {width height : ℕ}
    {v w : TorusVertex width height} :
    torusVerticalNeighbor (torusCoordinateSwapEquiv width height v)
      (torusCoordinateSwapEquiv width height w) ↔ torusHorizontalNeighbor v w :=
  Iff.rfl

/-- Coordinate swap exchanges vertical and horizontal cyclic neighbours. -/
theorem torusVerticalNeighbor_coordinateSwap {width height : ℕ}
    {v w : TorusVertex width height} :
    torusHorizontalNeighbor (torusCoordinateSwapEquiv width height v)
      (torusCoordinateSwapEquiv width height w) ↔ torusVerticalNeighbor v w :=
  Iff.rfl

/-- The image of a finite torus region under coordinate swap.  Unlike the graph
isomorphism below, this operation does not require nontrivial side lengths. -/
def torusCoordinateSwapRegion {width height : ℕ}
    (R : Finset (TorusVertex width height)) : Finset (TorusVertex height width) :=
  R.map (torusCoordinateSwapEquiv width height).toEmbedding

@[simp] theorem mem_torusCoordinateSwapRegion {width height : ℕ}
    (R : Finset (TorusVertex width height)) (v : TorusVertex height width) :
    v ∈ torusCoordinateSwapRegion R ↔ (v.2, v.1) ∈ R := by
  simp [torusCoordinateSwapRegion]

/-- Swapping both coordinates of a finite region returns the original region. -/
@[simp] theorem torusCoordinateSwapRegion_swap {width height : ℕ}
    (R : Finset (TorusVertex width height)) :
    torusCoordinateSwapRegion (torusCoordinateSwapRegion R) = R := by
  ext v
  simp only [mem_torusCoordinateSwapRegion]

/-- Coordinate swap transposes a contiguous rectangle and exchanges its side lengths. -/
theorem torusCoordinateSwapRegion_torusContiguousRectangle {width height : ℕ}
    [NeZero width] [NeZero height] (xStart yStart xLen yLen : ℕ) :
    torusCoordinateSwapRegion
        (torusContiguousRectangle xStart yStart xLen yLen :
          Finset (TorusVertex width height)) =
      (torusContiguousRectangle yStart xStart yLen xLen :
        Finset (TorusVertex height width)) := by
  ext v
  simp only [mem_torusCoordinateSwapRegion, mem_torusContiguousRectangle]
  tauto

/-! ### Coordinate swap of abstract region-injectivity data -/

/-- Pull region-injectivity data back along coordinate swap. -/
def RegionInjectivityData.coordinateSwap {width height : ℕ}
    (κ : RegionInjectivityData (TorusVertex width height)) :
    RegionInjectivityData (TorusVertex height width) where
  IsInjective R := κ.IsInjective (torusCoordinateSwapRegion R)

@[simp] theorem RegionInjectivityData.coordinateSwap_isInjective
    {width height : ℕ} (κ : RegionInjectivityData (TorusVertex width height))
    (R : Finset (TorusVertex height width)) :
    κ.coordinateSwap.IsInjective R ↔
      κ.IsInjective (torusCoordinateSwapRegion R) :=
  Iff.rfl

/-- Coordinate swap exchanges the two rectangular source shapes and hence
preserves the rectangular-injectivity hypotheses. -/
theorem NormalTorusRectangleInjectivityHypotheses.coordinateSwap
    {width height : ℕ} [NeZero width] [NeZero height]
    {κ : RegionInjectivityData (TorusVertex width height)}
    (h : NormalTorusRectangleInjectivityHypotheses κ) :
    NormalTorusRectangleInjectivityHypotheses κ.coordinateSwap where
  twoByThree_injective := by
    rintro R ⟨xStart, yStart, hx, hy, rfl⟩
    rw [RegionInjectivityData.coordinateSwap_isInjective,
      torusCoordinateSwapRegion_torusContiguousRectangle]
    exact h.rect32_injective hy hx
  threeByTwo_injective := by
    rintro R ⟨xStart, yStart, hx, hy, rfl⟩
    rw [RegionInjectivityData.coordinateSwap_isInjective,
      torusCoordinateSwapRegion_torusContiguousRectangle]
    exact h.rect23_injective hy hx

/-- Coordinate swap preserves closure of abstract region injectivity under unions. -/
theorem RegionInjectivityUnionClosure.coordinateSwap
    {width height : ℕ}
    {κ : RegionInjectivityData (TorusVertex width height)}
    (h : RegionInjectivityUnionClosure κ) :
    RegionInjectivityUnionClosure κ.coordinateSwap where
  union_injective := by
    intro R S hR hS
    change κ.IsInjective (torusCoordinateSwapRegion (R ∪ S))
    simpa only [torusCoordinateSwapRegion, Finset.map_union] using
      h.union_injective hR hS

variable {width height : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Interchanging coordinates as an isomorphism from the `width × height` torus graph
onto the `height × width` torus graph. -/
def torusCoordinateSwap :
    torusGraph width height ≃g torusGraph height width where
  toEquiv := torusCoordinateSwapEquiv width height
  map_rel_iff' := by
    intro v w
    rw [torusGraph_adj, torusGraph_adj]
    rw [torusHorizontalNeighbor_coordinateSwap, torusVerticalNeighbor_coordinateSwap,
      or_comm]

@[simp] theorem torusCoordinateSwap_apply (v : TorusVertex width height) :
    torusCoordinateSwap v = (v.2, v.1) :=
  rfl

@[simp] theorem torusCoordinateSwap_symm :
    (torusCoordinateSwap (width := width) (height := height)).symm =
      torusCoordinateSwap (width := height) (height := width) :=
  rfl

end PEPS
end TNLean
