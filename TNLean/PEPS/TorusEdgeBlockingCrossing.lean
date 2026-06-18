import TNLean.PEPS.TorusEdgeBlockingRegion
import TNLean.PEPS.TorusTranslationInvariant
import TNLean.PEPS.RegionBlock.CoarseThreeSite2

/-!
# The single red-to-blue crossing of the torus edge blocking

The coarse three-site route discharges the per-edge gauge from the single-crossing hypothesis
`∀ g, IsCrossingEdge A red blue g ↔ g = e`.  This file proves that hypothesis for the horizontal
and vertical edge blockings of `TNLean/PEPS/TorusEdgeBlockingRegion.lean`, where the red and blue
blocks meet only along the distinguished edge.

The discrete-torus subtlety over the open lattice is the cyclic adjacency: a horizontal step
`v.1 + 1 = w.1` is read in `ZMod width`.  Inside the bounding window of the blocking a cyclic step
either adds without wrapping (`val_add_of_lt`), where the open-lattice crossing argument carries
over, or wraps to the zero coordinate; a wrapped step cannot cross between the red and blue
blocks, because the zero column (row) lies strictly left of (below) both blocks whenever the
window starts at coordinate one or later.  The blocking may therefore touch the seam on the far
side (`xStart + 5 = width`, `yStart + 5 = height`), as it does at the anchor used for the
source's sizes `n, m ≥ 7`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)] {d : ℕ}

/-! ### Coordinate values of a cyclic step inside the no-wraparound window -/

omit [NeZero width] [NeZero height] [Fact (1 < height)] in
/-- A horizontal cyclic step `v.1 + 1 = w.1` reads as an ordinary coordinate step when the source
value plus one stays below the width. -/
theorem torus_horizontal_step_val {v w : TorusVertex width height} (h : v.1 + 1 = w.1)
    (hlt : v.1.val + 1 < width) :
    w.1.val = v.1.val + 1 := by
  rw [← h, ZMod.val_add_of_lt (by rw [ZMod.val_one]; omega), ZMod.val_one]

omit [NeZero height] [Fact (1 < height)] in
/-- A horizontal cyclic step `v.1 + 1 = w.1` wraps to the zero column when the source value is
the last column. -/
theorem torus_horizontal_step_val_wrap {v w : TorusVertex width height} (h : v.1 + 1 = w.1)
    (heq : v.1.val + 1 = width) :
    w.1.val = 0 := by
  rw [← h, ZMod.val_add, ZMod.val_one, heq, Nat.mod_self]

omit [NeZero width] [NeZero height] [Fact (1 < width)] in
/-- A vertical cyclic step `v.2 + 1 = w.2` reads as an ordinary coordinate step when the source
value plus one stays below the height. -/
theorem torus_vertical_step_val {v w : TorusVertex width height} (h : v.2 + 1 = w.2)
    (hlt : v.2.val + 1 < height) :
    w.2.val = v.2.val + 1 := by
  rw [← h, ZMod.val_add_of_lt (by rw [ZMod.val_one]; omega), ZMod.val_one]

omit [NeZero width] [Fact (1 < width)] in
/-- A vertical cyclic step `v.2 + 1 = w.2` wraps to the zero row when the source value is the
last row. -/
theorem torus_vertical_step_val_wrap {v w : TorusVertex width height} (h : v.2 + 1 = w.2)
    (heq : v.2.val + 1 = height) :
    w.2.val = 0 := by
  rw [← h, ZMod.val_add, ZMod.val_one, heq, Nat.mod_self]

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
/-- The horizontal coordinate value is preserved by a vertical cyclic step. -/
theorem torus_eq_fst_val {v w : TorusVertex width height} (h : v.1 = w.1) :
    v.1.val = w.1.val := by rw [h]

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
/-- The vertical coordinate value is preserved by a horizontal cyclic step. -/
theorem torus_eq_snd_val {v w : TorusVertex width height} (h : v.2 = w.2) :
    v.2.val = w.2.val := by rw [h]

/-! ### The reference horizontal and vertical edges -/

/-- The distinguished horizontal edge of the blocking at offset `(xStart, yStart)`: the edge from
`(xStart + 1, yStart + 2)` to `(xStart + 2, yStart + 2)`.  This is the only red-to-blue crossing. -/
def torusHorizontalReferenceEdge (xStart yStart : ℕ) : Edge (torusGraph width height) :=
  torusRightEdge ((xStart + 1 : ℕ), (yStart + 2 : ℕ))

/-- The distinguished vertical edge of the blocking at offset `(xStart, yStart)`: the edge from
`(xStart + 2, yStart + 1)` to `(xStart + 2, yStart + 2)`.  This is the only red-to-blue crossing. -/
def torusVerticalReferenceEdge (xStart yStart : ℕ) : Edge (torusGraph width height) :=
  torusUpEdge ((xStart + 2 : ℕ), (yStart + 1 : ℕ))

/-- Ordered endpoints of a torus right edge that avoids wraparound: the first endpoint is the lower
horizontal coordinate. -/
theorem torusRightEdge_endpoints_of_lt {p : TorusVertex width height}
    (hlt : p.1.val + 1 < width) :
    (torusRightEdge p).1.1 = p ∧ (torusRightEdge p).1.2 = (p.1 + 1, p.2) := by
  have hadj : (torusGraph width height).Adj p (p.1 + 1, p.2) := torusGraph_adj_right p.1 p.2
  have hcmp : p < ((p.1 + 1, p.2) : TorusVertex width height) := by
    change toLex (p.1.val, p.2.val) < toLex ((p.1 + 1).val, p.2.val)
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl (by rw [ZMod.val_add_of_lt (by rw [ZMod.val_one]; omega), ZMod.val_one]; omega)
  rw [torusRightEdge, Edge.ofAdj_of_lt hadj hcmp]
  exact ⟨rfl, rfl⟩

/-- Ordered endpoints of a torus up edge that avoids wraparound: the first endpoint is the lower
vertical coordinate. -/
theorem torusUpEdge_endpoints_of_lt {p : TorusVertex width height}
    (hlt : p.2.val + 1 < height) :
    (torusUpEdge p).1.1 = p ∧ (torusUpEdge p).1.2 = (p.1, p.2 + 1) := by
  have hadj : (torusGraph width height).Adj p (p.1, p.2 + 1) := torusGraph_adj_up p.1 p.2
  have hcmp : p < ((p.1, p.2 + 1) : TorusVertex width height) := by
    change toLex (p.1.val, p.2.val) < toLex (p.1.val, (p.2 + 1).val)
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inr ⟨rfl, by
      rw [ZMod.val_add_of_lt (by rw [ZMod.val_one]; omega), ZMod.val_one]
      omega⟩
  rw [torusUpEdge, Edge.ofAdj_of_lt hadj hcmp]
  exact ⟨rfl, rfl⟩

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- Two torus vertices with equal coordinate values are equal. -/
theorem torusVertex_eq_of_val_eq {v w : TorusVertex width height}
    (h1 : v.1.val = w.1.val) (h2 : v.2.val = w.2.val) : v = w :=
  Prod.ext (ZMod.val_injective width h1) (ZMod.val_injective height h2)

/-- The four endpoint coordinate values of the distinguished horizontal edge, when the offset
avoids wraparound. -/
theorem horizontalReferenceEdge_val {xStart yStart : ℕ}
    (hxw : xStart + 2 < width) (hyh : yStart + 2 < height) :
    (torusHorizontalReferenceEdge (width := width) (height := height) xStart yStart).1.1.1.val =
        xStart + 1 ∧
      (torusHorizontalReferenceEdge (width := width) (height := height) xStart yStart).1.1.2.val =
        yStart + 2 ∧
      (torusHorizontalReferenceEdge (width := width) (height := height) xStart yStart).1.2.1.val =
        xStart + 2 ∧
      (torusHorizontalReferenceEdge (width := width) (height := height)
        xStart yStart).1.2.2.val = yStart + 2 := by
  have href := torusRightEdge_endpoints_of_lt (p := ((xStart + 1 : ℕ), (yStart + 2 : ℕ)))
    (width := width) (height := height) (by rw [ZMod.val_cast_of_lt (by omega)]; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [torusHorizontalReferenceEdge, href.1]; exact ZMod.val_cast_of_lt (by omega)
  · rw [torusHorizontalReferenceEdge, href.1]; exact ZMod.val_cast_of_lt (by omega)
  · rw [torusHorizontalReferenceEdge, href.2]
    change ((xStart + 1 : ℕ) + 1 : ZMod width).val = xStart + 2
    rw [show ((xStart + 1 : ℕ) + 1 : ZMod width) = ((xStart + 2 : ℕ) : ZMod width) from by
      push_cast; ring]
    exact ZMod.val_cast_of_lt (by omega)
  · rw [torusHorizontalReferenceEdge, href.2]; exact ZMod.val_cast_of_lt (by omega)

/-! ### The single red-to-blue crossing of the horizontal edge blocking -/

/-- **The red-to-blue crossings of the horizontal torus edge blocking are the single distinguished
edge.**

The red block (the removed vertical edge block) and the blue block (the removed horizontal edge
block) meet only along the distinguished horizontal edge.  Hence an edge crosses between them iff it
is that edge.  The bounding window may touch the seam on the right and top (`xStart + 5 = width`,
`yStart + 5 = height`): a horizontal step wrapping the seam lands in the zero column, which lies
strictly left of both blocks since `1 ≤ xStart`, so a wrapped step never crosses.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_torusHorizontalEdge
    (A : Tensor (torusGraph width height) d) {xStart yStart : ℕ}
    (hx0 : 1 ≤ xStart) (hxw : xStart + 5 ≤ width) (hyh : yStart + 5 ≤ height)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (torusHorizontalEdgeRed xStart yStart) (torusHorizontalEdgeBlue xStart yStart) g ↔
      g = torusHorizontalReferenceEdge xStart yStart := by
  constructor
  · rintro ⟨hRed, hBlue⟩
    -- Both endpoints lie in the window: one in red, one in blue.
    simp only [IsRegionBoundaryEdge, mem_torusHorizontalEdgeRed, mem_torusHorizontalEdgeBlue]
      at hRed hBlue
    -- Both endpoints lie in the bounding window of the hole, so their coordinate values are
    -- below `xStart + 5 ≤ width` and `yStart + 5 ≤ height`.
    have hwin : g.1.1.1.val < xStart + 5 ∧ g.1.2.1.val < xStart + 5 ∧
        g.1.1.2.val < yStart + 5 ∧ g.1.2.2.val < yStart + 5 := by
      rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
        rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
        (simp only [not_and, not_lt] at hrn hbn ⊢; omega)
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hwin
    -- The ordered-endpoint convention `g.1.1 < g.1.2` in coordinate-value form.
    have hlt : g.1.1.1.val < g.1.2.1.val ∨
        (g.1.1.1.val = g.1.2.1.val ∧ g.1.1.2.val < g.1.2.2.val) := by
      have hlex : (g.1.1 : TorusVertex width height) < g.1.2 := g.2.1
      change toLex (g.1.1.1.val, g.1.1.2.val) < toLex (g.1.2.1.val, g.1.2.2.val) at hlex
      rw [Prod.Lex.toLex_lt_toLex] at hlex
      exact hlex
    -- The adjacency of `g`, a horizontal or vertical cyclic step.
    have hadj := g.2.2
    rw [torusGraph_adj, torusHorizontalNeighbor, torusVerticalNeighbor] at hadj
    -- Pin the four coordinate values of `g` to the distinguished edge's coordinates.  A
    -- horizontal step wrapping the seam lands in the zero column, left of both blocks.
    have hcoord : g.1.1.1.val = xStart + 1 ∧ g.1.1.2.val = yStart + 2 ∧
        g.1.2.1.val = xStart + 2 ∧ g.1.2.2.val = yStart + 2 := by
      rcases hadj with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
      · -- Horizontal step: same vertical coordinate, adjacent horizontal coordinates.
        have hrow' := torus_eq_snd_val hrow
        rcases hcol with hstep | hstep
        · by_cases hnowrap : g.1.1.1.val + 1 < width
          · have hxstep := torus_horizontal_step_val hstep hnowrap
            rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
              rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
              (simp only [not_and, not_lt] at hrn hbn; omega)
          · have hwrap : g.1.1.1.val + 1 = width := by
              have := ZMod.val_lt g.1.1.1
              omega
            have hxstep := torus_horizontal_step_val_wrap hstep hwrap
            rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
              rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
              (simp only [not_and, not_lt] at hrn hbn; omega)
        · by_cases hnowrap : g.1.2.1.val + 1 < width
          · have hxstep := torus_horizontal_step_val hstep hnowrap
            rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
              rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
              (simp only [not_and, not_lt] at hrn hbn; omega)
          · have hwrap : g.1.2.1.val + 1 = width := by
              have := ZMod.val_lt g.1.2.1
              omega
            have hxstep := torus_horizontal_step_val_wrap hstep hwrap
            rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
              rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
              (simp only [not_and, not_lt] at hrn hbn; omega)
      · -- Vertical step: same horizontal coordinate, but red and blue columns are disjoint.
        exfalso
        have hcol' := torus_eq_fst_val hcol
        rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
          rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
          (simp only [not_and, not_lt] at hrn hbn; omega)
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hcoord
    -- The reference edge's endpoint coordinate values.
    obtain ⟨hr11, hr12, hr21, hr22⟩ := horizontalReferenceEdge_val
      (width := width) (height := height) (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
    apply Subtype.ext
    refine Prod.ext (torusVertex_eq_of_val_eq ?_ ?_) (torusVertex_eq_of_val_eq ?_ ?_)
    · rw [hc1, hr11]
    · rw [hc2, hr12]
    · rw [hc3, hr21]
    · rw [hc4, hr22]
  · rintro rfl
    obtain ⟨hr11, hr12, hr21, hr22⟩ := horizontalReferenceEdge_val
      (width := width) (height := height) (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
    refine ⟨Or.inl ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [mem_torusHorizontalEdgeRed]; omega
    · rw [mem_torusHorizontalEdgeRed]; omega
    · rw [mem_torusHorizontalEdgeBlue]; omega
    · rw [mem_torusHorizontalEdgeBlue]; omega

/-- The four endpoint coordinate values of the distinguished vertical edge, when the offset avoids
wraparound. -/
theorem verticalReferenceEdge_val {xStart yStart : ℕ}
    (hxw : xStart + 2 < width) (hyh : yStart + 2 < height) :
    (torusVerticalReferenceEdge (width := width) (height := height) xStart yStart).1.1.1.val =
        xStart + 2 ∧
      (torusVerticalReferenceEdge (width := width) (height := height) xStart yStart).1.1.2.val =
        yStart + 1 ∧
      (torusVerticalReferenceEdge (width := width) (height := height) xStart yStart).1.2.1.val =
        xStart + 2 ∧
      (torusVerticalReferenceEdge (width := width) (height := height)
        xStart yStart).1.2.2.val = yStart + 2 := by
  have href := torusUpEdge_endpoints_of_lt (p := ((xStart + 2 : ℕ), (yStart + 1 : ℕ)))
    (width := width) (height := height) (by rw [ZMod.val_cast_of_lt (by omega)]; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [torusVerticalReferenceEdge, href.1]; exact ZMod.val_cast_of_lt (by omega)
  · rw [torusVerticalReferenceEdge, href.1]; exact ZMod.val_cast_of_lt (by omega)
  · rw [torusVerticalReferenceEdge, href.2]; exact ZMod.val_cast_of_lt (by omega)
  · rw [torusVerticalReferenceEdge, href.2]
    change ((yStart + 1 : ℕ) + 1 : ZMod height).val = yStart + 2
    rw [show ((yStart + 1 : ℕ) + 1 : ZMod height) = ((yStart + 2 : ℕ) : ZMod height) from by
      push_cast; ring]
    exact ZMod.val_cast_of_lt (by omega)

/-! ### The single red-to-blue crossing of the vertical edge blocking -/

/-- **The red-to-blue crossings of the vertical torus edge blocking are the single distinguished
edge.**

The rotated counterpart of `isCrossingEdge_torusHorizontalEdge`: the red block (the removed
horizontal edge block) and the blue block (the removed vertical edge block) meet only along the
distinguished vertical edge.  The bounding window may touch the seam on the right and top: a
vertical step wrapping the seam lands in the zero row, which lies strictly below both blocks
since `1 ≤ yStart`, so a wrapped step never crosses.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_torusVerticalEdge
    (A : Tensor (torusGraph width height) d) {xStart yStart : ℕ}
    (hy0 : 1 ≤ yStart) (hxw : xStart + 5 ≤ width) (hyh : yStart + 5 ≤ height)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (torusVerticalEdgeRed xStart yStart) (torusVerticalEdgeBlue xStart yStart) g ↔
      g = torusVerticalReferenceEdge xStart yStart := by
  constructor
  · rintro ⟨hRed, hBlue⟩
    simp only [IsRegionBoundaryEdge, mem_torusVerticalEdgeRed, mem_torusVerticalEdgeBlue]
      at hRed hBlue
    have hwin : g.1.1.1.val < xStart + 5 ∧ g.1.2.1.val < xStart + 5 ∧
        g.1.1.2.val < yStart + 5 ∧ g.1.2.2.val < yStart + 5 := by
      rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
        rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
        (simp only [not_and, not_lt] at hrn hbn ⊢; omega)
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hwin
    have hlt : g.1.1.1.val < g.1.2.1.val ∨
        (g.1.1.1.val = g.1.2.1.val ∧ g.1.1.2.val < g.1.2.2.val) := by
      have hlex : (g.1.1 : TorusVertex width height) < g.1.2 := g.2.1
      change toLex (g.1.1.1.val, g.1.1.2.val) < toLex (g.1.2.1.val, g.1.2.2.val) at hlex
      rw [Prod.Lex.toLex_lt_toLex] at hlex
      exact hlex
    have hadj := g.2.2
    rw [torusGraph_adj, torusHorizontalNeighbor, torusVerticalNeighbor] at hadj
    have hcoord : g.1.1.1.val = xStart + 2 ∧ g.1.1.2.val = yStart + 1 ∧
        g.1.2.1.val = xStart + 2 ∧ g.1.2.2.val = yStart + 2 := by
      rcases hadj with ⟨hrow, -⟩ | ⟨hcol, hrow⟩
      · -- Horizontal step: same vertical coordinate, but red and blue rows are disjoint.
        exfalso
        have hrow' := torus_eq_snd_val hrow
        rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
          rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
          (simp only [not_and, not_lt] at hrn hbn; omega)
      · -- Vertical step: same horizontal coordinate, adjacent vertical coordinates.  A step
        -- wrapping the seam lands in the zero row, below both blocks.
        have hcol' := torus_eq_fst_val hcol
        rcases hrow with hstep | hstep
        · by_cases hnowrap : g.1.1.2.val + 1 < height
          · have hystep := torus_vertical_step_val hstep hnowrap
            rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
              rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
              (simp only [not_and, not_lt] at hrn hbn; omega)
          · have hwrap : g.1.1.2.val + 1 = height := by
              have := ZMod.val_lt g.1.1.2
              omega
            have hystep := torus_vertical_step_val_wrap hstep hwrap
            rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
              rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
              (simp only [not_and, not_lt] at hrn hbn; omega)
        · by_cases hnowrap : g.1.2.2.val + 1 < height
          · have hystep := torus_vertical_step_val hstep hnowrap
            rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
              rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
              (simp only [not_and, not_lt] at hrn hbn; omega)
          · have hwrap : g.1.2.2.val + 1 = height := by
              have := ZMod.val_lt g.1.2.2
              omega
            have hystep := torus_vertical_step_val_wrap hstep hwrap
            rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
              rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
              (simp only [not_and, not_lt] at hrn hbn; omega)
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hcoord
    obtain ⟨hr11, hr12, hr21, hr22⟩ := verticalReferenceEdge_val
      (width := width) (height := height) (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
    apply Subtype.ext
    refine Prod.ext (torusVertex_eq_of_val_eq ?_ ?_) (torusVertex_eq_of_val_eq ?_ ?_)
    · rw [hc1, hr11]
    · rw [hc2, hr12]
    · rw [hc3, hr21]
    · rw [hc4, hr22]
  · rintro rfl
    obtain ⟨hr11, hr12, hr21, hr22⟩ := verticalReferenceEdge_val
      (width := width) (height := height) (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
    refine ⟨Or.inl ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [mem_torusVerticalEdgeRed]; omega
    · rw [mem_torusVerticalEdgeRed]; omega
    · rw [mem_torusVerticalEdgeBlue]; omega
    · rw [mem_torusVerticalEdgeBlue]; omega

end PEPS
end TNLean
