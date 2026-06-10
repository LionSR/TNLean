import TNLean.PEPS.NormalEdgeBlockingTranslated
import TNLean.PEPS.NormalRectangleTiling

/-!
# The cover-free every-edge blocking at interior edges

This file is the every-edge finite-geometry construction of the square-lattice
normal PEPS proof, with no rectangular-cover hypothesis.  The interior
edge-complement injectivity lemmas of `TNLean.PEPS.NormalRectangleTiling`
discharge the complementary-block injectivity directly, so the translated
edge-blocking data are built unconditionally at every edge whose endpoint lies in
the interior of a sufficiently large lattice.

The earlier translated edge-blocking data of `NormalEdgeBlockingTranslated` take
the complementary-block injectivity as a hypothesis, supplied there by a
rectangular cover of the complement.  The origin-window models have no such
cover (the notch corner is flush against the lattice corner), so that route
cannot reach the origin frame.  Here the cover is removed: the four surrounding
bands and two filler rectangles cover the interior complementary block, and
rectangular injectivity with the union-of-injective-regions lemma proves it
injective.  This realigns the local and rotated \(T\)-injectivity argument with
the finite PEPS geometry of the source, the obligation recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining
mathematical obligations".

The interior margin predicates demand one further row and column of room beyond
the cover route's bare \(5\times7\) (or \(7\times5\)) fit, because the interior
cover surrounds the removed L-shape on every side.  Edges near the lattice
boundary remain outside these predicates; that boundary geometry is the residual
open part of the every-edge construction in the present open rectangular model.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3, lines 1449--1500 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ}
variable {κ : RegionInjectivityData (SquareLatticeVertex width height)}

/-! ### Cover-free translated horizontal edge blocking -/

/-- A translated horizontal edge has red/blue/complement blocking data with no
rectangular-cover hypothesis.

The complementary block is the interior edge-complement region, which the
interior cover proves injective directly from rectangular injectivity and the
union-of-injective-regions lemma.  The frame offset `(xStart, yStart)` must have
two rows and columns of margin below and to the left and eight rows and columns
of total room, so the removed L-shape is surrounded on every side.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def normalSquareHorizontalTranslatedEdge_blockingDatum_interior
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height)
      (normalSquareHorizontalTranslatedEdge xStart yStart (by omega) (by omega)) :=
  normalSquareHorizontalTranslatedEdge_blockingDatum h (by omega) (by omega)
    (h.interiorEdgeComplement_injective hUnion hx0 hy0 hxw hyh)

/-! ### Cover-free translated vertical edge blocking -/

/-- A translated vertical edge has red/blue/complement blocking data with no
rectangular-cover hypothesis.

This is the rotated counterpart of
`normalSquareHorizontalTranslatedEdge_blockingDatum_interior`: the interior
vertical cover proves the rotated complementary block injective directly.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def normalSquareVerticalTranslatedEdge_blockingDatum_interior
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height)
      (normalSquareVerticalTranslatedEdge xStart yStart (by omega) (by omega)) :=
  normalSquareVerticalTranslatedEdge_blockingDatum h (by omega) (by omega)
    (h.interiorVerticalEdgeComplement_injective hUnion hx0 hy0 hxw hyh)

/-! ### Interior margin predicates and coordinate-edge data -/

/-- The interior horizontal margins of a coordinate right edge.

This is the cover-free strengthening of `IsNormalSquareHorizontalEdgeMargins`:
the right edge at `(x, y)` is placed by the translated frame at `(x-1, y-2)`, and
the interior cover demands two rows and columns of margin below and to the left
of that frame and eight rows and columns of total room.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def IsNormalSquareHorizontalEdgeInteriorMargins (width height x y : ℕ) : Prop :=
  3 ≤ x ∧ x + 7 ≤ width ∧ 4 ≤ y ∧ y + 6 ≤ height

/-- The interior vertical margins of a coordinate upward edge.

This is the cover-free strengthening of `IsNormalSquareVerticalEdgeMargins`: the
upward edge at `(x, y)` is placed by the translated frame at `(x-2, y-1)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def IsNormalSquareVerticalEdgeInteriorMargins (width height x y : ℕ) : Prop :=
  4 ≤ x ∧ x + 6 ≤ width ∧ 3 ≤ y ∧ y + 7 ≤ height

/-- A coordinate right edge with interior margins has cover-free blocking data.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def squareLatticeRightEdge_blockingDatum_interior
    {x y : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hMargins : IsNormalSquareHorizontalEdgeInteriorMargins width height x y) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height)
      (squareLatticeRightEdge (width := width) (height := height)
        x y (by rcases hMargins with ⟨_, hxR, _, _⟩; omega)
              (by rcases hMargins with ⟨_, _, _, hyT⟩; omega)) := by
  obtain ⟨hxL, hxR, hyB, hyT⟩ := hMargins
  rw [← normalSquareHorizontalTranslatedEdge_sub_eq_rightEdge
    (by omega) (by omega) (by omega) (by omega)]
  exact normalSquareHorizontalTranslatedEdge_blockingDatum_interior h hUnion
    (by omega) (by omega) (by omega) (by omega)

/-- A coordinate upward edge with interior margins has cover-free blocking data.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def squareLatticeUpEdge_blockingDatum_interior
    {x y : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hMargins : IsNormalSquareVerticalEdgeInteriorMargins width height x y) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height)
      (squareLatticeUpEdge (width := width) (height := height)
        x y (by rcases hMargins with ⟨_, hxR, _, _⟩; omega)
              (by rcases hMargins with ⟨_, _, _, hyT⟩; omega)) := by
  obtain ⟨hxL, hxR, hyB, hyT⟩ := hMargins
  rw [← normalSquareVerticalTranslatedEdge_sub_eq_upEdge
    (by omega) (by omega) (by omega) (by omega)]
  exact normalSquareVerticalTranslatedEdge_blockingDatum_interior h hUnion
    (by omega) (by omega) (by omega) (by omega)

/-! ### Interior blocking data at arbitrary oriented edges -/

/-- A horizontal square-lattice edge with interior margins has cover-free
blocking data.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def horizontalSquareLatticeEdge_blockingDatum_interior
    (e : Edge (squareLatticeGraph width height))
    (hEdge : IsHorizontalSquareLatticeEdge e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hMargins :
      IsNormalSquareHorizontalEdgeInteriorMargins width height e.1.1.1.1 e.1.1.2.1) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height) e := by
  rw [horizontalSquareLatticeEdge_eq_rightEdge e hEdge]
  exact squareLatticeRightEdge_blockingDatum_interior h hUnion hMargins

/-- A vertical square-lattice edge with interior margins has cover-free blocking
data.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def verticalSquareLatticeEdge_blockingDatum_interior
    (e : Edge (squareLatticeGraph width height))
    (hEdge : IsVerticalSquareLatticeEdge e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hMargins :
      IsNormalSquareVerticalEdgeInteriorMargins width height e.1.1.1.1 e.1.1.2.1) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height) e := by
  rw [verticalSquareLatticeEdge_eq_upEdge e hEdge]
  exact squareLatticeUpEdge_blockingDatum_interior h hUnion hMargins

/-! ### The cover-free every-edge bundle -/

/-- Cover-free interior blocking input for one edge.

An edge is either horizontal with interior horizontal margins or vertical with
interior vertical margins.  Either way the interior cover discharges the
complementary-block injectivity, so no rectangular cover is recorded.  This is
the cover-free counterpart of `NormalSquareEdgeMarginCover`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
inductive NormalSquareInteriorEdgeDatum {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) : Prop
  | horizontal
      (hEdge : IsHorizontalSquareLatticeEdge e)
      (hMargins :
        IsNormalSquareHorizontalEdgeInteriorMargins width height e.1.1.1.1 e.1.1.2.1)
  | vertical
      (hEdge : IsVerticalSquareLatticeEdge e)
      (hMargins :
        IsNormalSquareVerticalEdgeInteriorMargins width height e.1.1.1.1 e.1.1.2.1)

/-- The cover-free interior datum gives one-edge blocking data for its edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def NormalSquareInteriorEdgeDatum.blockingDatum
    {e : Edge (squareLatticeGraph width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (datum : NormalSquareInteriorEdgeDatum e) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height) e := by
  by_cases hHor : IsHorizontalSquareLatticeEdge e
  · refine horizontalSquareLatticeEdge_blockingDatum_interior e hHor h hUnion ?_
    rcases datum with ⟨_, hMargins⟩ | ⟨hVer, _⟩
    · exact hMargins
    · exact absurd ⟨hHor, hVer⟩ (squareLatticeEdge_not_horizontal_and_vertical e)
  · have hVer : IsVerticalSquareLatticeEdge e :=
      (squareLatticeEdge_horizontal_or_vertical e).resolve_left hHor
    refine verticalSquareLatticeEdge_blockingDatum_interior e hVer h hUnion ?_
    rcases datum with ⟨hHor', _⟩ | ⟨_, hMargins⟩
    · exact absurd hHor' hHor
    · exact hMargins

/-- **The cover-free every-edge blocking hypotheses.**

If every edge of the finite square lattice carries the cover-free interior datum
— is horizontal or vertical with the corresponding interior margins — then the
normal edge-blocking hypotheses hold with no rectangular-cover input anywhere.
The complementary block at each edge is injective by the interior cover.

This is the source-faithful every-edge blocking for the interior edges of a
sufficiently large lattice.  The residual open part is the boundary geometry of
the open rectangular model, where some edges lack interior margins, recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining
mathematical obligations".

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def normalSquareEdgeBlockingHypotheses_of_interiorData
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareInteriorEdgeDatum e) :
    NormalEdgeBlockingHypotheses κ (squareLatticeGraph width height) :=
  NormalEdgeBlockingHypotheses.ofBlockingData fun e =>
    (data e).blockingDatum h hUnion

/-- The cover-free every-edge hypotheses give the three injective regions at
every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeBlockingHypotheses_of_interiorData_injective_chain
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareInteriorEdgeDatum e)
    (e : Edge (squareLatticeGraph width height)) :
    κ.IsInjective ((normalSquareEdgeBlockingHypotheses_of_interiorData
        h hUnion data).red e) ∧
      κ.IsInjective ((normalSquareEdgeBlockingHypotheses_of_interiorData
        h hUnion data).blue e) ∧
      κ.IsInjective ((normalSquareEdgeBlockingHypotheses_of_interiorData
        h hUnion data).complement e) :=
  (normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).injective_chain_at_edge e

/-- The cover-free every-edge hypotheses record endpoint membership, pairwise
disjointness, and coverage at every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeBlockingHypotheses_of_interiorData_endpoint_disjoint_cover
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareInteriorEdgeDatum e)
    (e : Edge (squareLatticeGraph width height)) :
    e.1.1 ∈ (normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).red e ∧
      e.1.2 ∈ (normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).blue e ∧
      Disjoint ((normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).red e)
        ((normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).blue e) ∧
      Disjoint ((normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).red e)
        ((normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).complement e) ∧
      Disjoint ((normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).blue e)
        ((normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).complement e) ∧
      (normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).red e ∪
          (normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).blue e ∪
            (normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).complement e =
        (Finset.univ : Finset (SquareLatticeVertex width height)) :=
  (normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).endpoint_disjoint_cover_at_edge
    e

end PEPS
end TNLean
