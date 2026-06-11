import TNLean.PEPS.TorusEdgeBlockingCrossing
import TNLean.PEPS.NormalEdgeBlockingData

/-!
# The faithful torus reference blocking datum from rectangle injectivity

For a torus tensor whose contiguous $2\times3$ and $3\times2$ blocks are injective (the source's own
blocking hypotheses) and whose region injectivity is union closed, the distinguished horizontal and
vertical reference edges carry a one-edge blocking datum: the red block is the removed source
rectangle, the blue block is the other removed source rectangle, and the complementary block is the
union of four surrounding bands and two fillers.  All three are injective by rectangular injectivity
and the union-of-injective-regions lemma, they partition the torus, and their single red-to-blue
crossing is the reference edge.

This is the source-faithful reference blocking datum the translation-invariant gauge family
consumes.  Unlike the vertex-injective singleton datum of
`TNLean/PEPS/TorusReferenceBlockingData.lean`, the injectivity inputs are exactly the source's
rectangular-injectivity hypotheses, with no single-vertex injectivity.  The reference edge sits in
the interior of the torus with enough margin that the regions avoid the wraparound seam.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-! ### The faithful horizontal reference blocking datum -/

/-- **Faithful horizontal reference blocking datum on the torus.**

For a torus tensor `A` whose region-injectivity predicate satisfies the rectangular-injectivity
hypotheses and union closure, the distinguished horizontal reference edge carries the one-edge
blocking datum whose red block is the removed vertical edge block, blue block the removed horizontal
edge block, and complementary block the rest of the torus.  All three are injective by rectangular
injectivity and the union-of-injective-regions lemma; they partition the torus; the edge's left
endpoint lies in red and its right endpoint in blue.

The offset `(xStart, yStart)` must place the regions clear of the wraparound seam: at least two
columns and one row of margin below and to the left, and enough room above and to the right.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusHorizontalRectangleBlockingDatum
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 7 ≤ width) (hyh : yStart + 7 ≤ height) :
    NormalEdgeBlockingData κ (torusGraph width height)
      (torusHorizontalReferenceEdge xStart yStart) where
  red := torusHorizontalEdgeRed xStart yStart
  blue := torusHorizontalEdgeBlue xStart yStart
  complement := torusHorizontalEdgeComplement xStart yStart
  left_mem_red := by
    obtain ⟨hr11, hr12, _, _⟩ :=
      horizontalReferenceEdge_val (width := width) (height := height)
        (xStart := xStart) (yStart := yStart) (by omega) (by omega)
    rw [mem_torusHorizontalEdgeRed]; omega
  right_mem_blue := by
    obtain ⟨_, _, hr21, hr22⟩ :=
      horizontalReferenceEdge_val (width := width) (height := height)
        (xStart := xStart) (yStart := yStart) (by omega) (by omega)
    rw [mem_torusHorizontalEdgeBlue]; omega
  red_injective := h.horizontalEdgeRed_injective (by omega) (by omega)
  blue_injective := h.horizontalEdgeBlue_injective (by omega) (by omega)
  complement_injective := h.horizontalEdgeComplement_injective hUnion hx0 hy0 hxw hyh
  red_disjoint_blue := torusHorizontalEdgeRed_disjoint_blue xStart yStart
  red_disjoint_complement := torusHorizontalEdgeRed_disjoint_complement xStart yStart
  blue_disjoint_complement := torusHorizontalEdgeBlue_disjoint_complement xStart yStart
  cover_univ := torusHorizontalEdge_cover_univ xStart yStart

@[simp] theorem torusHorizontalRectangleBlockingDatum_red
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 7 ≤ width) (hyh : yStart + 7 ≤ height) :
    (torusHorizontalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).red =
      torusHorizontalEdgeRed xStart yStart := rfl

@[simp] theorem torusHorizontalRectangleBlockingDatum_blue
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 7 ≤ width) (hyh : yStart + 7 ≤ height) :
    (torusHorizontalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).blue =
      torusHorizontalEdgeBlue xStart yStart := rfl

/-- The red-to-blue crossings of the faithful horizontal reference datum are exactly the
distinguished horizontal reference edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_torusHorizontalRectangleBlockingDatum
    (A : Tensor (torusGraph width height) d)
    {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUnion : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 5 < width) (hyh : yStart + 5 < height)
    (hxw' : xStart + 7 ≤ width) (hyh' : yStart + 7 ≤ height)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (torusHorizontalRectangleBlockingDatum h hUnion hx0 hy0 hxw' hyh').red
        (torusHorizontalRectangleBlockingDatum h hUnion hx0 hy0 hxw' hyh').blue g ↔
      g = torusHorizontalReferenceEdge xStart yStart := by
  rw [torusHorizontalRectangleBlockingDatum_red, torusHorizontalRectangleBlockingDatum_blue]
  exact isCrossingEdge_torusHorizontalEdge A hxw hyh g

/-! ### The faithful vertical reference blocking datum -/

/-- **Faithful vertical reference blocking datum on the torus.**

The vertical counterpart of `torusHorizontalRectangleBlockingDatum` at the distinguished vertical
reference edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusVerticalRectangleBlockingDatum
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 7 ≤ width) (hyh : yStart + 7 ≤ height) :
    NormalEdgeBlockingData κ (torusGraph width height)
      (torusVerticalReferenceEdge xStart yStart) where
  red := torusVerticalEdgeRed xStart yStart
  blue := torusVerticalEdgeBlue xStart yStart
  complement := torusVerticalEdgeComplement xStart yStart
  left_mem_red := by
    obtain ⟨hr11, hr12, _, _⟩ :=
      verticalReferenceEdge_val (width := width) (height := height)
        (xStart := xStart) (yStart := yStart) (by omega) (by omega)
    rw [mem_torusVerticalEdgeRed]; omega
  right_mem_blue := by
    obtain ⟨_, _, hr21, hr22⟩ :=
      verticalReferenceEdge_val (width := width) (height := height)
        (xStart := xStart) (yStart := yStart) (by omega) (by omega)
    rw [mem_torusVerticalEdgeBlue]; omega
  red_injective := h.verticalEdgeRed_injective (by omega) (by omega)
  blue_injective := h.verticalEdgeBlue_injective (by omega) (by omega)
  complement_injective := h.verticalEdgeComplement_injective hUnion hx0 hy0 hxw hyh
  red_disjoint_blue := torusVerticalEdgeRed_disjoint_blue xStart yStart
  red_disjoint_complement := torusVerticalEdgeRed_disjoint_complement xStart yStart
  blue_disjoint_complement := torusVerticalEdgeBlue_disjoint_complement xStart yStart
  cover_univ := torusVerticalEdge_cover_univ xStart yStart

@[simp] theorem torusVerticalRectangleBlockingDatum_red
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 7 ≤ width) (hyh : yStart + 7 ≤ height) :
    (torusVerticalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).red =
      torusVerticalEdgeRed xStart yStart := rfl

@[simp] theorem torusVerticalRectangleBlockingDatum_blue
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 7 ≤ width) (hyh : yStart + 7 ≤ height) :
    (torusVerticalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).blue =
      torusVerticalEdgeBlue xStart yStart := rfl

/-- The red-to-blue crossings of the faithful vertical reference datum are exactly the
distinguished vertical reference edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_torusVerticalRectangleBlockingDatum
    (A : Tensor (torusGraph width height) d)
    {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUnion : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 5 < width) (hyh : yStart + 5 < height)
    (hxw' : xStart + 7 ≤ width) (hyh' : yStart + 7 ≤ height)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (torusVerticalRectangleBlockingDatum h hUnion hx0 hy0 hxw' hyh').red
        (torusVerticalRectangleBlockingDatum h hUnion hx0 hy0 hxw' hyh').blue g ↔
      g = torusVerticalReferenceEdge xStart yStart := by
  rw [torusVerticalRectangleBlockingDatum_red, torusVerticalRectangleBlockingDatum_blue]
  exact isCrossingEdge_torusVerticalEdge A hxw hyh g

end PEPS
end TNLean
