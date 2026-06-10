import TNLean.PEPS.NormalEdgeComplementCover

/-!
# Tiling injectivity for the normal PEPS edge-complement block

This file supplies the finite-geometry injectivity argument that the
square-lattice normal PEPS proof needs for the complementary block \(A_3\)
around an edge.  It is the realignment recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining
mathematical obligations", obligations on the local and rotated \(T\)-regions
and the every-edge construction.

The origin-window models of the displayed \(T\)-region and of \(A_3\) have no
exact cover by contiguous \(2\times3\) and \(3\times2\) rectangles
(`not_normalSquareRegionT_rectangleCover_at_origin` and its siblings): the
notch corner of the removed L-shape is flush against the lattice corner, and no
contained rectangle of either source shape reaches it.  The source proof,
however, blocks around an edge *in the interior* of a sufficiently large
lattice, where the removed L-shape is surrounded on every side.  In that
interior placement the complementary block is a union of contiguous rectangles,
each of which avoids the removed blocks, so the union-of-injective-regions
lemma proves it injective with no exact-cover obstruction.

The development has two layers.  First, any contiguous rectangle whose two side
lengths are at least the source shapes is injective, because it is a finite
union of the source \(2\times3\) (or \(3\times2\)) rectangles.  Second, the
interior edge-complement block is the union of four full-length bands around the
removed L-shape together with two small filler rectangles, all of which avoid
the removed blocks; combining the rectangle injectivity with union closure gives
injectivity of the interior complementary block.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Lemma `injective_union` and Theorem 3, lines 1322--1500 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

namespace NormalSquareLatticeRectangleInjectivityHypotheses

variable {width height : ℕ}
variable {κ : RegionInjectivityData (SquareLatticeVertex width height)}

/-! ### Injectivity of a large contiguous rectangle -/

/-- A wide-or-tall contiguous rectangle is the union of contiguous source
\(2\times3\) rectangles sliding over it.

A contiguous `xLen × yLen` rectangle with `xLen ≥ 2` and `yLen ≥ 3` is the union
of the `2×3` windows whose lower-left corners range over the contained offsets.
Every cell of the rectangle lies in one such window.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1430 of `Papers/1804.04964/paper_normal.tex`. -/
theorem contiguousRectangle_eq_biUnion_two_by_three
    (xStart yStart xLen yLen : ℕ) (hx : 2 ≤ xLen) (hy : 3 ≤ yLen) :
    (squareLatticeContiguousRectangle xStart yStart xLen yLen :
        Finset (SquareLatticeVertex width height)) =
      (Finset.range (xLen - 1) ×ˢ Finset.range (yLen - 2)).biUnion
        (fun p => squareLatticeContiguousRectangle (xStart + p.1) (yStart + p.2) 2 3) := by
  ext v
  simp only [mem_squareLatticeContiguousRectangle, Finset.mem_biUnion, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    refine ⟨(min (v.1.1 - xStart) (xLen - 2), min (v.2.1 - yStart) (yLen - 3)), ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, hv⟩
    omega

/-- A wide-or-tall contiguous rectangle is injective.

If every contiguous source \(2\times3\) rectangle is injective and the
union-of-injective-regions lemma holds, then a contiguous `xLen × yLen`
rectangle with `xLen ≥ 2` and `yLen ≥ 3` is injective: it is the finite union of
the contained \(2\times3\) windows.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1452 of `Papers/1804.04964/paper_normal.tex`. -/
theorem wideRectangle_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart xLen yLen : ℕ}
    (hx : 2 ≤ xLen) (hy : 3 ≤ yLen)
    (hxw : xStart + xLen ≤ width) (hyh : yStart + yLen ≤ height) :
    κ.IsInjective
      (squareLatticeContiguousRectangle xStart yStart xLen yLen :
        Finset (SquareLatticeVertex width height)) := by
  rw [contiguousRectangle_eq_biUnion_two_by_three xStart yStart xLen yLen hx hy]
  refine hUnion.biUnion_injective ?_ _ ?_
  · exact ⟨(0, 0), by simp [Finset.mem_product, Finset.mem_range]; omega⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, Finset.mem_range] at hab
    exact h.rect23_injective (by omega) (by omega)

/-- A wide-and-short contiguous rectangle is the union of contiguous source
\(3\times2\) rectangles sliding over it.

A contiguous `xLen × yLen` rectangle with `xLen ≥ 3` and `yLen ≥ 2` is the union
of the `3×2` windows whose lower-left corners range over the contained offsets.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1430 of `Papers/1804.04964/paper_normal.tex`. -/
theorem contiguousRectangle_eq_biUnion_three_by_two
    (xStart yStart xLen yLen : ℕ) (hx : 3 ≤ xLen) (hy : 2 ≤ yLen) :
    (squareLatticeContiguousRectangle xStart yStart xLen yLen :
        Finset (SquareLatticeVertex width height)) =
      (Finset.range (xLen - 2) ×ˢ Finset.range (yLen - 1)).biUnion
        (fun p => squareLatticeContiguousRectangle (xStart + p.1) (yStart + p.2) 3 2) := by
  ext v
  simp only [mem_squareLatticeContiguousRectangle, Finset.mem_biUnion, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    refine ⟨(min (v.1.1 - xStart) (xLen - 3), min (v.2.1 - yStart) (yLen - 2)), ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, hv⟩
    omega

/-- A wide-and-short contiguous rectangle is injective.

If every contiguous source \(3\times2\) rectangle is injective and the
union-of-injective-regions lemma holds, then a contiguous `xLen × yLen`
rectangle with `xLen ≥ 3` and `yLen ≥ 2` is injective.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1452 of `Papers/1804.04964/paper_normal.tex`. -/
theorem shortRectangle_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart xLen yLen : ℕ}
    (hx : 3 ≤ xLen) (hy : 2 ≤ yLen)
    (hxw : xStart + xLen ≤ width) (hyh : yStart + yLen ≤ height) :
    κ.IsInjective
      (squareLatticeContiguousRectangle xStart yStart xLen yLen :
        Finset (SquareLatticeVertex width height)) := by
  rw [contiguousRectangle_eq_biUnion_three_by_two xStart yStart xLen yLen hx hy]
  refine hUnion.biUnion_injective ?_ _ ?_
  · exact ⟨(0, 0), by simp [Finset.mem_product, Finset.mem_range]; omega⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, Finset.mem_range] at hab
    exact h.rect32_injective (by omega) (by omega)

end NormalSquareLatticeRectangleInjectivityHypotheses

/-! ### The interior edge-complement cover -/

/-- The six rectangular pieces covering the interior edge-complement block.

For an L-shaped hole placed at the interior offset `(x0, y0)`, the complement of
the removed blocks in the `width × height` lattice is the union of four
full-length bands surrounding the hole — below, above, left, and right — together
with two filler rectangles inside the hole's bounding box.  Each piece avoids the
removed blocks.

The bands are:

* the bottom band of all rows strictly below the hole,
* the top band of all rows strictly above the hole,
* the left band of all columns strictly left of the hole,
* the right band of all columns strictly right of the hole.

The fillers are the contiguous \(2\times3\) rectangle reaching down from the
notch below the vertical block, and the contiguous \(3\times2\) rectangle above
the horizontal block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500 of
`Papers/1804.04964/paper_normal.tex`, where the complementary block \(A_3\)
around an interior edge is injective. -/
def interiorEdgeComplementPiece {width height : ℕ} (x0 y0 : ℕ) :
    Fin 6 → Finset (SquareLatticeVertex width height)
  | 0 => squareLatticeContiguousRectangle 0 0 width (y0 + 1)
  | 1 => squareLatticeContiguousRectangle 0 (y0 + 5) width (height - (y0 + 5))
  | 2 => squareLatticeContiguousRectangle 0 0 x0 height
  | 3 => squareLatticeContiguousRectangle (x0 + 5) 0 (width - (x0 + 5)) height
  | 4 => squareLatticeContiguousRectangle x0 (y0 - 1) 2 3
  | 5 => squareLatticeContiguousRectangle (x0 + 2) (y0 + 3) 3 2

/-- The interior edge-complement block is the union of the six covering pieces.

For an interior offset `(x0, y0)` with one row and one column of margin below and
to the left and two further rows and columns of room above and to the right, the
complement of the removed L-shape is exactly the union of the four surrounding
bands and the two fillers.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeComplementRegion_eq_biUnion_interiorPieces {width height : ℕ}
    {x0 y0 : ℕ} (hy0 : 1 ≤ y0) (hxw : x0 + 5 ≤ width) (hyh : y0 + 5 ≤ height) :
    (normalSquareEdgeComplementRegion (width := width) (height := height) x0 y0) =
      (Finset.univ : Finset (Fin 6)).biUnion (interiorEdgeComplementPiece x0 y0) := by
  ext v
  simp only [mem_normalSquareEdgeComplementRegion, mem_normalSquareRegionTHole, not_or, not_and,
    not_lt, Finset.mem_biUnion, Finset.mem_univ, true_and]
  have hvx : v.1.1 < width := v.1.2
  have hvy : v.2.1 < height := v.2.2
  constructor
  · intro hv
    by_cases hb : v.2.1 < y0 + 1
    · exact ⟨0, by simp [interiorEdgeComplementPiece]; omega⟩
    by_cases ht : y0 + 5 ≤ v.2.1
    · exact ⟨1, by simp [interiorEdgeComplementPiece]; omega⟩
    by_cases hl : v.1.1 < x0
    · exact ⟨2, by simp [interiorEdgeComplementPiece]; omega⟩
    by_cases hr : x0 + 5 ≤ v.1.1
    · exact ⟨3, by simp [interiorEdgeComplementPiece]; omega⟩
    -- now v is inside the bounding box of the hole
    by_cases hf1 : v.1.1 < x0 + 2
    · exact ⟨4, by simp [interiorEdgeComplementPiece]; omega⟩
    · exact ⟨5, by simp [interiorEdgeComplementPiece]; omega⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;>
      · simp only [interiorEdgeComplementPiece, mem_squareLatticeContiguousRectangle] at hi
        omega

namespace NormalSquareLatticeRectangleInjectivityHypotheses

variable {width height : ℕ}
variable {κ : RegionInjectivityData (SquareLatticeVertex width height)}

/-- **The interior edge-complement block is injective, unconditionally.**

When the removed L-shape sits in the interior of a sufficiently large lattice —
at least one row and column of margin below and to the left, and at least three
rows and columns of room above and to the right — the complementary block
\(A_3\) is the union of four surrounding bands and two filler rectangles, each of
which is a contiguous rectangle avoiding the removed blocks.  Rectangular
injectivity together with the union-of-injective-regions lemma proves it
injective, with no exact-cover obstruction and no \(T\)-cover hypothesis.

This is the source-faithful injectivity of the complementary block \(A_3\),
realigning the local-window argument with the finite PEPS geometry as recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem interiorEdgeComplement_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {x0 y0 : ℕ} (hx0 : 2 ≤ x0) (hy0 : 2 ≤ y0)
    (hxw : x0 + 8 ≤ width) (hyh : y0 + 8 ≤ height) :
    κ.IsInjective
      (normalSquareEdgeComplementRegion (width := width) (height := height) x0 y0) := by
  rw [normalSquareEdgeComplementRegion_eq_biUnion_interiorPieces (by omega) (by omega) (by omega)]
  refine hUnion.biUnion_injective ⟨0, Finset.mem_univ _⟩ _ ?_
  intro i _
  fin_cases i
  · -- bottom band: width × (y0 + 1), short rectangle (width ≥ 3, height y0 + 1 ≥ 2)
    exact h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- top band: width × (height - (y0 + 5)), short rectangle
    exact h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- left band: x0 × height, wide rectangle (x0 ≥ 2, height ≥ 3)
    exact h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- right band: (width - (x0 + 5)) × height, wide rectangle
    exact h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- first filler: 2 × 3
    exact h.rect23_injective (by omega) (by omega)
  · -- second filler: 3 × 2
    exact h.rect32_injective (by omega) (by omega)

end NormalSquareLatticeRectangleInjectivityHypotheses

end PEPS
end TNLean
