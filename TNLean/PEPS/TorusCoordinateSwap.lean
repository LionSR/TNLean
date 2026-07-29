/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionTransport
import TNLean.PEPS.TorusWindowComplement

/-!
# Coordinate swap on the discrete torus

Interchanging the two coordinates identifies the `width × height` torus with the
`height × width` torus. This file records the graph isomorphism and the covariance
of cyclic rectangles under that isomorphism. These lemmas let proofs for horizontal
windows be reused for their vertical transposes.
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

/-- Coordinate swap preserves unions of finite regions. -/
@[deprecated "Expand `torusCoordinateSwapRegion` and use `Finset.map_union`."
  (since := "2026-07-30")]
theorem torusCoordinateSwapRegion_union {width height : ℕ}
    (R S : Finset (TorusVertex width height)) :
    torusCoordinateSwapRegion (R ∪ S) =
      torusCoordinateSwapRegion R ∪ torusCoordinateSwapRegion S := by
  ext v
  simp only [mem_torusCoordinateSwapRegion, Finset.mem_union]

/-- Coordinate swap commutes with finite indexed unions. -/
theorem torusCoordinateSwapRegion_biUnion {width height : ℕ} {ι : Type*}
    (s : Finset ι) (R : ι → Finset (TorusVertex width height)) :
    torusCoordinateSwapRegion (s.biUnion R) =
      s.biUnion (fun i => torusCoordinateSwapRegion (R i)) := by
  ext v
  simp only [mem_torusCoordinateSwapRegion, Finset.mem_biUnion]

/-- Coordinate swap preserves inclusion of finite regions. -/
theorem torusCoordinateSwapRegion_mono {width height : ℕ}
    {R S : Finset (TorusVertex width height)} (h : R ⊆ S) :
    torusCoordinateSwapRegion R ⊆ torusCoordinateSwapRegion S := by
  intro v hv
  rw [mem_torusCoordinateSwapRegion] at hv ⊢
  exact h hv

/-- Swapping both coordinates of a finite region returns the original region. -/
@[simp] theorem torusCoordinateSwapRegion_swap {width height : ℕ}
    (R : Finset (TorusVertex width height)) :
    torusCoordinateSwapRegion (torusCoordinateSwapRegion R) = R := by
  ext v
  simp only [mem_torusCoordinateSwapRegion]

/-- Coordinate swap transposes a cyclic rectangle and exchanges its side lengths. -/
theorem torusCoordinateSwapRegion_torusArcRectangle {width height : ℕ}
    [NeZero width] [NeZero height] (s : TorusVertex width height) (xLen yLen : ℕ) :
    torusCoordinateSwapRegion (torusArcRectangle s xLen yLen) =
      torusArcRectangle (s.2, s.1) yLen xLen := by
  ext v
  simp only [mem_torusCoordinateSwapRegion, mem_torusArcRectangle]
  exact and_comm

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

/-- Coordinate swap sends horizontal edges to vertical edges. -/
@[deprecated "Use `torusHorizontalNeighbor_coordinateSwap` together with
`Edge.map_endpoints`." (since := "2026-07-30")]
theorem torusCoordinateSwap_isVertical {e : Edge (torusGraph width height)}
    (he : IsHorizontalTorusEdge e) :
    IsVerticalTorusEdge (Edge.map torusCoordinateSwap e) := by
  have h := (torusHorizontalNeighbor_coordinateSwap (v := e.1.1) (w := e.1.2)).mpr he
  rcases Edge.map_endpoints torusCoordinateSwap e with hends | hends
  · unfold IsVerticalTorusEdge
    rw [show (Edge.map torusCoordinateSwap e).1.1 = torusCoordinateSwap e.1.1 from hends.1,
      show (Edge.map torusCoordinateSwap e).1.2 = torusCoordinateSwap e.1.2 from hends.2]
    exact h
  · unfold IsVerticalTorusEdge
    rw [show (Edge.map torusCoordinateSwap e).1.1 = torusCoordinateSwap e.1.2 from hends.1,
      show (Edge.map torusCoordinateSwap e).1.2 = torusCoordinateSwap e.1.1 from hends.2]
    exact torusVerticalNeighbor_symm h

/-- Coordinate swap sends vertical edges to horizontal edges. -/
@[deprecated "Use `torusVerticalNeighbor_coordinateSwap` together with
`Edge.map_endpoints`." (since := "2026-07-30")]
theorem torusCoordinateSwap_isHorizontal {e : Edge (torusGraph width height)}
    (he : IsVerticalTorusEdge e) :
    IsHorizontalTorusEdge (Edge.map torusCoordinateSwap e) := by
  have h := (torusVerticalNeighbor_coordinateSwap (v := e.1.1) (w := e.1.2)).mpr he
  rcases Edge.map_endpoints torusCoordinateSwap e with hends | hends
  · unfold IsHorizontalTorusEdge
    rw [show (Edge.map torusCoordinateSwap e).1.1 = torusCoordinateSwap e.1.1 from hends.1,
      show (Edge.map torusCoordinateSwap e).1.2 = torusCoordinateSwap e.1.2 from hends.2]
    exact h
  · unfold IsHorizontalTorusEdge
    rw [show (Edge.map torusCoordinateSwap e).1.1 = torusCoordinateSwap e.1.2 from hends.1,
      show (Edge.map torusCoordinateSwap e).1.2 = torusCoordinateSwap e.1.1 from hends.2]
    exact torusHorizontalNeighbor_symm h

end PEPS
end TNLean
