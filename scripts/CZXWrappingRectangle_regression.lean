import TNLean.PEPS.Examples.CZXWrappingRectangle

/-! Actual-name regressions for cyclic coordinate rectangles. These test the
region itself crossing each seam, the faithful map and the printed operator,
and strict properness at maximal lengths. -/

open TNLean.PEPS
open scoped Matrix

local instance : Fact (2 < 5) := ⟨by decide⟩
local instance : Fact (2 < 6) := ⟨by decide⟩
local instance : Fact (1 < 5) := ⟨by decide⟩
local instance : Fact (1 < 6) := ⟨by decide⟩

-- Horizontal wrapping: the region contains both columns 4 and 0.
example : ((0, 2) : TorusVertex 5 6) ∈ torusArcRectangle (4, 1) 2 3 := by decide
example : ((4, 2) : TorusVertex 5 6) ∈ torusArcRectangle (4, 1) 2 3 := by decide
example : ((1, 2) : TorusVertex 5 6) ∉ torusArcRectangle (4, 1) 2 3 := by decide

example : Function.Injective
    (czxWrappingRectangleBoundaryMatrix (width := 5) (height := 6)
      (4, 1) 2 3 (by decide) (by decide) (by decide) (by decide)).mulVec :=
  czxWrappingRectangleBoundaryMatrix_mulVec_injective (4, 1) 2 3
    (by decide) (by decide) (by decide) (by decide)

-- Vertical wrapping: rows 5 and 0 are both in the coordinate interval.
example : ((2, 0) : TorusVertex 5 6) ∈ torusArcRectangle (1, 5) 2 2 := by decide
example : ((2, 5) : TorusVertex 5 6) ∈ torusArcRectangle (1, 5) 2 2 := by decide
example : (regionReducedDensity (czxPEPS 5 6)
    (torusArcRectangle (1, 5) 2 2)).rank = 2 ^ 8 := by
  exact rank_regionReducedDensity_czxWrappingRectangle (1, 5) 2 2
    (by decide) (by decide) (by decide) (by decide)

-- Both seams, with the printed MPO acting on the literal actual map.
example : ((0, 0) : TorusVertex 5 6) ∈ torusArcRectangle (4, 5) 2 2 := by decide

-- The top and bottom really are the translated native crossing bonds.
example : (czxWrappingRectanglePerimeterEquiv ((4, 5) : TorusVertex 5 6)
    2 2 (by decide) (by decide) (by decide) (by decide) 0).1 = torusUpEdge (4, 0) := by
  rw [czxWrappingRectanglePerimeterEquiv_apply_val]
  change Edge.map (translate (4 : ZMod 5) (5 : ZMod 6)) (torusUpEdge (0, 1)) = _
  rw [← translateEdge_eq_map, translateEdge_torusUpEdge]
  rfl

example : (czxWrappingRectanglePerimeterEquiv ((4, 5) : TorusVertex 5 6)
    2 2 (by decide) (by decide) (by decide) (by decide) 4).1 = torusUpEdge (0, 4) := by
  rw [czxWrappingRectanglePerimeterEquiv_apply_val]
  change Edge.map (translate (4 : ZMod 5) (5 : ZMod 6)) (torusUpEdge (1, -1)) = _
  rw [← translateEdge_eq_map, translateEdge_torusUpEdge]
  rfl

example : czxWrappingRectangleCoordinatesEquiv ((4, 5) : TorusVertex 5 6)
    2 2 (by decide) (by decide) (by decide) (by decide)
      (fun _ => czxBond (0, 1)) 4 = czxBond (1, 0) := by
  simpa using (czxWrappingRectangleCoordinatesEquiv_apply
    ((4, 5) : TorusVertex 5 6) 2 2
    (by decide) (by decide) (by decide) (by decide) (fun _ => czxBond (0, 1)) 4)

example : regionPhysicalProductMatrix (torusArcRectangle (4, 5) 2 2)
      (fun _ => czxOnSite) *
      czxWrappingRectangleBoundaryMatrix (width := 5) (height := 6)
        (4, 5) 2 2 (by decide) (by decide) (by decide) (by decide) =
    czxWrappingRectangleBoundaryMatrix (4, 5) 2 2
        (by decide) (by decide) (by decide) (by decide) *
      MPOTensor.mpo CZXCompression.reviewCZXTensor 8 := by
  exact regionPhysicalProductMatrix_czxWrappingRectangleBoundaryMatrix_review
    (4, 5) 2 2 (by decide) (by decide) (by decide) (by decide)

-- Nonwrapping specialization uses the existing bounded region, exactly.
example : torusArcRectangle ((1, 2) : TorusVertex 5 6) 2 3 =
    torusContiguousRectangle 1 2 2 3 :=
  torusArcRectangle_eq_torusContiguousRectangle 1 2 2 3
    (by decide) (by decide) (by decide) (by decide)

example : (regionReducedDensity (czxPEPS 5 6)
    (torusContiguousRectangle 1 2 2 3)).rank = 2 ^ 10 := by
  rw [← torusArcRectangle_eq_torusContiguousRectangle 1 2 2 3
    (by decide) (by decide) (by decide) (by decide)]
  exact rank_regionReducedDensity_czxWrappingRectangle (1, 2) 2 3
    (by decide) (by decide) (by decide) (by decide)

-- Maximal proper lengths remain disks, with 18 independent boundary spins.
example : ((0, 0) : TorusVertex 5 6) ∈ torusArcRectangle (4, 5) 4 5 := by decide
example : ((3, 0) : TorusVertex 5 6) ∉ torusArcRectangle (4, 5) 4 5 := by decide
example : (regionReducedDensity (czxPEPS 5 6)
    (torusArcRectangle (4, 5) 4 5)).rank = 2 ^ 18 := by
  exact rank_regionReducedDensity_czxWrappingRectangle (4, 5) 4 5
    (by decide) (by decide) (by decide) (by decide)

-- The actual crossing-bond enumeration has exactly P elements at both seams.
example : Fintype.card
    {e : Edge (torusGraph 5 6) // IsRegionBoundaryEdge (torusArcRectangle (4, 5) 4 5) e} = 18 := by
  simpa using (Fintype.card_congr
    (czxWrappingRectanglePerimeterEquiv ((4, 5) : TorusVertex 5 6) 4 5
      (by decide) (by decide) (by decide) (by decide))).symm
