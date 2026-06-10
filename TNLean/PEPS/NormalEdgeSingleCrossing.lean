import TNLean.PEPS.NormalEdgeBlockingInterior
import TNLean.PEPS.RegionBlock.CoarseThreeSite2

/-!
# The single red-to-blue crossing of the translated edge blocking

The coarse three-site route discharges the per-edge gauge from the single-crossing
hypothesis `∀ g, IsCrossingEdge A red blue g ↔ g = e`: the red-to-blue crossings of
the edge blocking are exactly the distinguished edge `e`.  This file proves that
hypothesis from the coordinate geometry of the translated horizontal and vertical
edge blockings, where the red block is the removed vertical (respectively rotated
horizontal) edge block and the blue block is the removed horizontal (respectively
rotated vertical) edge block, the two blocks meeting only along `e`.

For the horizontal blocking the red block occupies the two columns
`xStart, xStart + 1` and the rows `yStart + 2, …, yStart + 4`; the blue block
occupies the three columns `xStart + 2, …, xStart + 4` and the rows
`yStart + 1, yStart + 2`.  The only nearest-neighbour pair with one endpoint in each
is `(xStart + 1, yStart + 2)`--`(xStart + 2, yStart + 2)`, the distinguished edge.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1449--1500 of `Papers/1804.04964/paper_normal.tex`; the red and
  blue blocks share exactly the distinguished edge](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} {d : ℕ}

/-! ### The single red-to-blue crossing of the translated horizontal edge -/

/-- **The red-to-blue crossings of the translated horizontal edge blocking are the
single distinguished edge.**

The red block (the removed vertical edge block) and the blue block (the removed
horizontal edge block) of the translated horizontal edge blocking meet only along the
distinguished edge `normalSquareHorizontalTranslatedEdge`.  Hence an edge crosses
between them if and only if it is that edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_normalSquareHorizontalTranslatedEdge
    (A : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height)
    (g : Edge (squareLatticeGraph width height)) :
    IsCrossingEdge (G := squareLatticeGraph width height) A
        (normalSquareHorizontalTranslatedEdgeRed xStart yStart)
        (normalSquareHorizontalTranslatedEdgeBlue xStart yStart) g ↔
      g = normalSquareHorizontalTranslatedEdge xStart yStart hx hy := by
  constructor
  · rintro ⟨hRed, hBlue⟩
    -- `g` crosses red (one endpoint in, one out) and blue (one endpoint in, one out).
    -- Unfold boundary membership and the nearest-neighbour adjacency of `g`.
    simp only [IsRegionBoundaryEdge, normalSquareHorizontalTranslatedEdgeRed,
      normalSquareHorizontalTranslatedEdgeBlue, mem_normalSquareRegionTVerticalBlock,
      mem_normalSquareRegionTHorizontalBlock] at hRed hBlue
    have hadj := g.2.2
    rw [squareLatticeGraph_adj, squareLatticeHorizontalNeighbor,
      squareLatticeVerticalNeighbor] at hadj
    -- The ordered-endpoint convention `g.1.1 < g.1.2` in coordinate form.
    have hlt : g.1.1.1.1 < g.1.2.1.1 ∨
        (g.1.1.1.1 = g.1.2.1.1 ∧ g.1.1.2.1 < g.1.2.2.1) := by
      have hlex : toLex g.1.1 < toLex g.1.2 := g.2.1
      rw [Prod.Lex.toLex_lt_toLex] at hlex
      rcases hlex with hx | ⟨hxe, hye⟩
      · exact Or.inl hx
      · exact Or.inr ⟨congrArg Fin.val hxe, hye⟩
    -- The four endpoint coordinates of `g` as naturals, with the row/column equalities
    -- of the nearest-neighbour step turned into natural equalities.
    have hyeq : ∀ {p q : Fin height}, p = q → p.1 = q.1 := fun h => congrArg Fin.val h
    have hxeq : ∀ {p q : Fin width}, p = q → p.1 = q.1 := fun h => congrArg Fin.val h
    -- Pin the two endpoints to the two flush coordinates of the distinguished edge.
    apply Subtype.ext
    -- It suffices to match all four endpoint coordinates.
    have hcoord : g.1.1.1.1 = xStart + 1 ∧ g.1.1.2.1 = yStart + 2 ∧
        g.1.2.1.1 = xStart + 2 ∧ g.1.2.2.1 = yStart + 2 := by
      rcases hadj with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
      · -- Horizontal step: same row, adjacent columns.
        have hrow' := hyeq hrow
        rcases hRed with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ <;>
          rcases hBlue with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
      · -- Vertical step: same column, but red columns and blue columns are disjoint.
        exfalso
        have hcol' := hxeq hcol
        rcases hRed with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ <;>
          rcases hBlue with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hcoord
    refine Prod.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
    · simpa only [normalSquareHorizontalTranslatedEdge] using hc1
    · simpa only [normalSquareHorizontalTranslatedEdge] using hc2
    · simpa only [normalSquareHorizontalTranslatedEdge] using hc3
    · simpa only [normalSquareHorizontalTranslatedEdge] using hc4
  · rintro rfl
    refine ⟨?_, ?_⟩ <;>
      simp only [IsRegionBoundaryEdge, normalSquareHorizontalTranslatedEdgeRed,
        normalSquareHorizontalTranslatedEdgeBlue, normalSquareHorizontalTranslatedEdge,
        mem_normalSquareRegionTVerticalBlock, mem_normalSquareRegionTHorizontalBlock]
    · exact Or.inl ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩
    · exact Or.inr ⟨by omega, ⟨by omega, by omega, by omega, by omega⟩⟩

/-! ### The single red-to-blue crossing of the translated vertical edge -/

/-- **The red-to-blue crossings of the translated vertical edge blocking are the
single distinguished edge.**

The rotated counterpart of
`isCrossingEdge_normalSquareHorizontalTranslatedEdge`.  The red block (the removed
horizontal edge block) occupies the three columns `xStart + 2, …, xStart + 4` and the
two rows `yStart, yStart + 1`; the blue block (the removed vertical edge block)
occupies the two columns `xStart + 1, xStart + 2` and the three rows
`yStart + 2, …, yStart + 4`.  The only nearest-neighbour pair with one endpoint in
each is `(xStart + 2, yStart + 1)`--`(xStart + 2, yStart + 2)`, the distinguished
edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_normalSquareVerticalTranslatedEdge
    (A : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height)
    (g : Edge (squareLatticeGraph width height)) :
    IsCrossingEdge (G := squareLatticeGraph width height) A
        (normalSquareVerticalTranslatedEdgeRed xStart yStart)
        (normalSquareVerticalTranslatedEdgeBlue xStart yStart) g ↔
      g = normalSquareVerticalTranslatedEdge xStart yStart hx hy := by
  constructor
  · rintro ⟨hRed, hBlue⟩
    simp only [IsRegionBoundaryEdge, normalSquareVerticalTranslatedEdgeRed,
      normalSquareVerticalTranslatedEdgeBlue, mem_squareLatticeContiguousRectangle] at hRed hBlue
    have hadj := g.2.2
    rw [squareLatticeGraph_adj, squareLatticeHorizontalNeighbor,
      squareLatticeVerticalNeighbor] at hadj
    have hlt : g.1.1.1.1 < g.1.2.1.1 ∨
        (g.1.1.1.1 = g.1.2.1.1 ∧ g.1.1.2.1 < g.1.2.2.1) := by
      have hlex : toLex g.1.1 < toLex g.1.2 := g.2.1
      rw [Prod.Lex.toLex_lt_toLex] at hlex
      rcases hlex with hxlt | ⟨hxe, hye⟩
      · exact Or.inl hxlt
      · exact Or.inr ⟨congrArg Fin.val hxe, hye⟩
    have hyeq : ∀ {p q : Fin height}, p = q → p.1 = q.1 := fun h => congrArg Fin.val h
    have hxeq : ∀ {p q : Fin width}, p = q → p.1 = q.1 := fun h => congrArg Fin.val h
    apply Subtype.ext
    have hcoord : g.1.1.1.1 = xStart + 2 ∧ g.1.1.2.1 = yStart + 1 ∧
        g.1.2.1.1 = xStart + 2 ∧ g.1.2.2.1 = yStart + 2 := by
      rcases hadj with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
      · -- Horizontal step: same row, but red rows and blue rows are disjoint.
        exfalso
        have hrow' := hyeq hrow
        rcases hRed with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ <;>
          rcases hBlue with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
      · -- Vertical step: same column, adjacent rows.
        have hcol' := hxeq hcol
        rcases hRed with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ <;>
          rcases hBlue with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hcoord
    refine Prod.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
    · simpa only [normalSquareVerticalTranslatedEdge] using hc1
    · simpa only [normalSquareVerticalTranslatedEdge] using hc2
    · simpa only [normalSquareVerticalTranslatedEdge] using hc3
    · simpa only [normalSquareVerticalTranslatedEdge] using hc4
  · rintro rfl
    refine ⟨?_, ?_⟩ <;>
      simp only [IsRegionBoundaryEdge, normalSquareVerticalTranslatedEdgeRed,
        normalSquareVerticalTranslatedEdgeBlue, normalSquareVerticalTranslatedEdge,
        mem_squareLatticeContiguousRectangle]
    · exact Or.inl ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩
    · exact Or.inr ⟨by omega, ⟨by omega, by omega, by omega, by omega⟩⟩

/-! ### The single-crossing hypothesis for the interior blocking data

The cover-free interior blocking data of `NormalEdgeBlockingInterior` carry the same
red, blue, and complement regions as the translated edge blockings (the interior
datum is the translated datum with the complementary-block injectivity discharged by
the interior cover).  Hence the red-to-blue crossings of the interior data are the
single distinguished edge, the single-crossing hypothesis the coarse three-site route
consumes. -/

variable {κ : RegionInjectivityData (SquareLatticeVertex width height)}

/-- The translated horizontal interior blocking data have the distinguished edge as
their only red-to-blue crossing.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_horizontalTranslatedEdge_blockingDatum_interior
    (A : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height)
    (g : Edge (squareLatticeGraph width height)) :
    IsCrossingEdge (G := squareLatticeGraph width height) A
        (normalSquareHorizontalTranslatedEdge_blockingDatum_interior
          h hUnion hx0 hy0 hxw hyh).red
        (normalSquareHorizontalTranslatedEdge_blockingDatum_interior
          h hUnion hx0 hy0 hxw hyh).blue g ↔
      g = normalSquareHorizontalTranslatedEdge xStart yStart (by omega) (by omega) :=
  isCrossingEdge_normalSquareHorizontalTranslatedEdge A (by omega) (by omega) g

/-- The translated vertical interior blocking data have the distinguished edge as
their only red-to-blue crossing.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_verticalTranslatedEdge_blockingDatum_interior
    (A : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height)
    (g : Edge (squareLatticeGraph width height)) :
    IsCrossingEdge (G := squareLatticeGraph width height) A
        (normalSquareVerticalTranslatedEdge_blockingDatum_interior
          h hUnion hx0 hy0 hxw hyh).red
        (normalSquareVerticalTranslatedEdge_blockingDatum_interior
          h hUnion hx0 hy0 hxw hyh).blue g ↔
      g = normalSquareVerticalTranslatedEdge xStart yStart (by omega) (by omega) :=
  isCrossingEdge_normalSquareVerticalTranslatedEdge A (by omega) (by omega) g

end PEPS
end TNLean
