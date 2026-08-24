/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NormalEdgeBlockingTranslatedCoordinate
/-!
# Translated edge blockings in the normal PEPS proof

This file records the coordinate-origin-parametric horizontal and vertical
edge-blocking pictures used after the normalized one-edge constructions.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3]
-/

namespace TNLean.PEPS

/-! ### Edge windows for the every-edge construction -/

universe edgeCoverUniverse

/-- A proof that an edge is realized by one of the translated normal
edge-blocking windows.

The constructors deliberately record the rectangular cover of the complementary
region. The source comparison and every-edge window elimination plan are
recorded in `docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section
"Remaining mathematical obligations".

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
inductive NormalSquareTranslatedEdgeWindow {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) : Type (edgeCoverUniverse + 1)
  | horizontal (xStart yStart : ℕ)
      (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
      (edge_eq :
        normalSquareHorizontalTranslatedEdge xStart yStart (by omega) (by omega) = e)
      (cover : NormalSquareEdgeComplementRectangleCover.{edgeCoverUniverse}
        (width := width) (height := height) xStart yStart)
  | vertical (xStart yStart : ℕ)
      (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
      (edge_eq :
        normalSquareVerticalTranslatedEdge xStart yStart (by omega) (by omega) = e)
      (cover : NormalSquareVerticalEdgeComplementRectangleCover.{edgeCoverUniverse}
        (width := width) (height := height) xStart yStart)

namespace NormalSquareTranslatedEdgeWindow

/-- A translated edge window gives the one-edge blocking datum for its edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def blockingDatum
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {e : Edge (squareLatticeGraph width height)}
    (w : NormalSquareTranslatedEdgeWindow e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height) e :=
  match w with
  | horizontal _xStart _yStart hx hy edge_eq cover =>
      edge_eq ▸
        normalSquareHorizontalTranslatedEdge_blockingDatum_of_complementCover
          h hUnion hx hy cover
  | vertical _xStart _yStart hx hy edge_eq cover =>
      edge_eq ▸
        normalSquareVerticalTranslatedEdge_blockingDatum_of_complementCover
          h hUnion hx hy cover

/-- A translated edge window supplies the three injective regions for its
edge-blocked chain.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem injective_chain
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {e : Edge (squareLatticeGraph width height)}
    (w : NormalSquareTranslatedEdgeWindow e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) :
    κ.IsInjective ((w.blockingDatum h hUnion).red) ∧
      κ.IsInjective ((w.blockingDatum h hUnion).blue) ∧
      κ.IsInjective ((w.blockingDatum h hUnion).complement) :=
  (w.blockingDatum h hUnion).injective_chain

/-- A translated edge window supplies endpoint membership, pairwise
disjointness, and coverage by its three blocking regions.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem endpoint_disjoint_cover
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {e : Edge (squareLatticeGraph width height)}
    (w : NormalSquareTranslatedEdgeWindow e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) :
    e.1.1 ∈ (w.blockingDatum h hUnion).red ∧
      e.1.2 ∈ (w.blockingDatum h hUnion).blue ∧
      Disjoint ((w.blockingDatum h hUnion).red) ((w.blockingDatum h hUnion).blue) ∧
      Disjoint ((w.blockingDatum h hUnion).red)
        ((w.blockingDatum h hUnion).complement) ∧
      Disjoint ((w.blockingDatum h hUnion).blue)
        ((w.blockingDatum h hUnion).complement) ∧
      (w.blockingDatum h hUnion).red ∪ (w.blockingDatum h hUnion).blue ∪
          (w.blockingDatum h hUnion).complement =
        (Finset.univ : Finset (SquareLatticeVertex width height)) :=
  (w.blockingDatum h hUnion).endpoint_disjoint_cover

end NormalSquareTranslatedEdgeWindow

/-- A translated horizontal window around a coordinate right edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareHorizontalTranslatedEdgeWindow
    {width height : ℕ} (xStart yStart : ℕ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) xStart yStart) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := width) (height := height)
        (xStart + 1) (yStart + 2) (by omega) (by omega)) :=
  NormalSquareTranslatedEdgeWindow.horizontal xStart yStart hx hy
    (normalSquareHorizontalTranslatedEdge_eq_rightEdge (by omega) (by omega)) cover

/-- A translated vertical window around a coordinate upward edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalTranslatedEdgeWindow
    {width height : ℕ} (xStart yStart : ℕ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (cover : NormalSquareVerticalEdgeComplementRectangleCover
      (width := width) (height := height) xStart yStart) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := width) (height := height)
        (xStart + 2) (yStart + 1) (by omega) (by omega)) :=
  NormalSquareTranslatedEdgeWindow.vertical xStart yStart hx hy
    (normalSquareVerticalTranslatedEdge_eq_upEdge (by omega) (by omega)) cover

/-- The coordinate inequalities needed to place the translated horizontal
edge-blocking frame around a coordinate right edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def IsNormalSquareHorizontalEdgeMargins (width height x y : ℕ) : Prop :=
  1 ≤ x ∧ x + 4 ≤ width ∧ 2 ≤ y ∧ y + 3 ≤ height

/-- The coordinate inequalities needed to place the translated vertical
edge-blocking frame around a coordinate upward edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def IsNormalSquareVerticalEdgeMargins (width height x y : ℕ) : Prop :=
  2 ≤ x ∧ x + 3 ≤ width ∧ 1 ≤ y ∧ y + 4 ≤ height

/-- A coordinate right edge with the required margins is the translated
horizontal edge whose frame starts at \((x-1,y-2)\).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareHorizontalTranslatedEdge_sub_eq_rightEdge
    {width height : ℕ} {x y : ℕ}
    (hxLeft : 1 ≤ x) (hxRight : x + 4 ≤ width)
    (hyBottom : 2 ≤ y) (hyTop : y + 3 ≤ height) :
    normalSquareHorizontalTranslatedEdge
        (width := width) (height := height) (x - 1) (y - 2)
        (by omega) (by omega) =
      squareLatticeRightEdge (width := width) (height := height)
        x y (by omega) (by omega) := by
  ext <;> simp [normalSquareHorizontalTranslatedEdge, squareLatticeRightEdge]
  all_goals omega

/-- A coordinate right edge admits the translated horizontal window when the
edge has enough room to place the normalized \(5\times7\) blocking frame around
it.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def squareLatticeRightEdgeWindow
    {width height : ℕ} (x y : ℕ)
    (hxLeft : 1 ≤ x) (hxRight : x + 4 ≤ width)
    (hyBottom : 2 ≤ y) (hyTop : y + 3 ≤ height)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) (x - 1) (y - 2)) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := width) (height := height)
        x y (by omega) (by omega)) :=
  NormalSquareTranslatedEdgeWindow.horizontal (x - 1) (y - 2)
    (by omega) (by omega)
    (normalSquareHorizontalTranslatedEdge_sub_eq_rightEdge
      hxLeft hxRight hyBottom hyTop)
    cover

/-- A coordinate right edge admits the translated horizontal window from the
named horizontal margin predicate.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def squareLatticeRightEdgeWindow_of_margins
    {width height : ℕ} (x y : ℕ)
    (hMargins : IsNormalSquareHorizontalEdgeMargins width height x y)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) (x - 1) (y - 2)) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := width) (height := height)
        x y
        (by
          rcases hMargins with ⟨_hxLeft, hxRight, _hyBottom, _hyTop⟩
          omega)
        (by
          rcases hMargins with ⟨_hxLeft, _hxRight, _hyBottom, hyTop⟩
          omega)) :=
  squareLatticeRightEdgeWindow x y
    hMargins.1 hMargins.2.1 hMargins.2.2.1 hMargins.2.2.2 cover

/-- A coordinate upward edge with the required margins is the translated
vertical edge whose frame starts at \((x-2,y-1)\).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalTranslatedEdge_sub_eq_upEdge
    {width height : ℕ} {x y : ℕ}
    (hxLeft : 2 ≤ x) (hxRight : x + 3 ≤ width)
    (hyBottom : 1 ≤ y) (hyTop : y + 4 ≤ height) :
    normalSquareVerticalTranslatedEdge
        (width := width) (height := height) (x - 2) (y - 1)
        (by omega) (by omega) =
      squareLatticeUpEdge (width := width) (height := height)
        x y (by omega) (by omega) := by
  ext <;> simp [normalSquareVerticalTranslatedEdge, squareLatticeUpEdge]
  all_goals omega

/-- A coordinate upward edge admits the translated vertical window when the
edge has enough room to place the normalized \(7\times5\) blocking frame around
it.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def squareLatticeUpEdgeWindow
    {width height : ℕ} (x y : ℕ)
    (hxLeft : 2 ≤ x) (hxRight : x + 3 ≤ width)
    (hyBottom : 1 ≤ y) (hyTop : y + 4 ≤ height)
    (cover : NormalSquareVerticalEdgeComplementRectangleCover
      (width := width) (height := height) (x - 2) (y - 1)) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := width) (height := height)
        x y (by omega) (by omega)) :=
  NormalSquareTranslatedEdgeWindow.vertical (x - 2) (y - 1)
    (by omega) (by omega)
    (normalSquareVerticalTranslatedEdge_sub_eq_upEdge
      hxLeft hxRight hyBottom hyTop)
    cover

/-- A coordinate upward edge admits the translated vertical window from the
named vertical margin predicate.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def squareLatticeUpEdgeWindow_of_margins
    {width height : ℕ} (x y : ℕ)
    (hMargins : IsNormalSquareVerticalEdgeMargins width height x y)
    (cover : NormalSquareVerticalEdgeComplementRectangleCover
      (width := width) (height := height) (x - 2) (y - 1)) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := width) (height := height)
        x y
        (by
          rcases hMargins with ⟨_hxLeft, hxRight, _hyBottom, _hyTop⟩
          omega)
        (by
          rcases hMargins with ⟨_hxLeft, _hxRight, _hyBottom, hyTop⟩
          omega)) :=
  squareLatticeUpEdgeWindow x y
    hMargins.1 hMargins.2.1 hMargins.2.2.1 hMargins.2.2.2 cover

/-- A horizontal square-lattice edge admits a translated horizontal window when
its ordered left endpoint has the required margins.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def horizontalSquareLatticeEdgeWindow
    {width height : ℕ} (e : Edge (squareLatticeGraph width height))
    (hEdge : IsHorizontalSquareLatticeEdge e)
    (hxLeft : 1 ≤ e.1.1.1.1) (hxRight : e.1.1.1.1 + 4 ≤ width)
    (hyBottom : 2 ≤ e.1.1.2.1) (hyTop : e.1.1.2.1 + 3 ≤ height)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) (e.1.1.1.1 - 1) (e.1.1.2.1 - 2)) :
    NormalSquareTranslatedEdgeWindow e := by
  rw [horizontalSquareLatticeEdge_eq_rightEdge e hEdge]
  exact squareLatticeRightEdgeWindow e.1.1.1.1 e.1.1.2.1
    hxLeft hxRight hyBottom hyTop cover

/-- A horizontal square-lattice edge admits a translated horizontal window from
the named horizontal margin predicate.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def horizontalSquareLatticeEdgeWindow_of_margins
    {width height : ℕ} (e : Edge (squareLatticeGraph width height))
    (hEdge : IsHorizontalSquareLatticeEdge e)
    (hMargins :
      IsNormalSquareHorizontalEdgeMargins width height e.1.1.1.1 e.1.1.2.1)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) (e.1.1.1.1 - 1) (e.1.1.2.1 - 2)) :
    NormalSquareTranslatedEdgeWindow e :=
  horizontalSquareLatticeEdgeWindow e hEdge
    hMargins.1 hMargins.2.1 hMargins.2.2.1 hMargins.2.2.2 cover

/-- A vertical square-lattice edge admits a translated vertical window when its
ordered lower endpoint has the required margins.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def verticalSquareLatticeEdgeWindow
    {width height : ℕ} (e : Edge (squareLatticeGraph width height))
    (hEdge : IsVerticalSquareLatticeEdge e)
    (hxLeft : 2 ≤ e.1.1.1.1) (hxRight : e.1.1.1.1 + 3 ≤ width)
    (hyBottom : 1 ≤ e.1.1.2.1) (hyTop : e.1.1.2.1 + 4 ≤ height)
    (cover : NormalSquareVerticalEdgeComplementRectangleCover
      (width := width) (height := height) (e.1.1.1.1 - 2) (e.1.1.2.1 - 1)) :
    NormalSquareTranslatedEdgeWindow e := by
  rw [verticalSquareLatticeEdge_eq_upEdge e hEdge]
  exact squareLatticeUpEdgeWindow e.1.1.1.1 e.1.1.2.1
    hxLeft hxRight hyBottom hyTop cover

/-- A vertical square-lattice edge admits a translated vertical window from
the named vertical margin predicate.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def verticalSquareLatticeEdgeWindow_of_margins
    {width height : ℕ} (e : Edge (squareLatticeGraph width height))
    (hEdge : IsVerticalSquareLatticeEdge e)
    (hMargins :
      IsNormalSquareVerticalEdgeMargins width height e.1.1.1.1 e.1.1.2.1)
    (cover : NormalSquareVerticalEdgeComplementRectangleCover
      (width := width) (height := height) (e.1.1.1.1 - 2) (e.1.1.2.1 - 1)) :
    NormalSquareTranslatedEdgeWindow e :=
  verticalSquareLatticeEdgeWindow e hEdge
    hMargins.1 hMargins.2.1 hMargins.2.2.1 hMargins.2.2.2 cover

/-- Per-edge data sufficient to realize a square-lattice edge by a translated
normal edge-blocking window.

This records the per-edge finite-geometry input in the current rectangular
coordinate model: an edge must be horizontal or vertical, have the corresponding
named margins, and have a rectangular cover for its complementary block. The
source comparison and every-edge window elimination plan are recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining
mathematical obligations".

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
inductive NormalSquareEdgeMarginCover {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) : Type (edgeCoverUniverse + 1)
  | horizontal
      (hEdge : IsHorizontalSquareLatticeEdge e)
      (hMargins :
        IsNormalSquareHorizontalEdgeMargins width height e.1.1.1.1 e.1.1.2.1)
      (cover : NormalSquareEdgeComplementRectangleCover.{edgeCoverUniverse}
        (width := width) (height := height) (e.1.1.1.1 - 1) (e.1.1.2.1 - 2))
  | vertical
      (hEdge : IsVerticalSquareLatticeEdge e)
      (hMargins :
        IsNormalSquareVerticalEdgeMargins width height e.1.1.1.1 e.1.1.2.1)
      (cover : NormalSquareVerticalEdgeComplementRectangleCover.{edgeCoverUniverse}
        (width := width) (height := height) (e.1.1.1.1 - 2) (e.1.1.2.1 - 1))

namespace NormalSquareEdgeMarginCover

/-- The translated edge window obtained from oriented margin-and-cover data.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def window {width height : ℕ} {e : Edge (squareLatticeGraph width height)}
    (d : NormalSquareEdgeMarginCover e) :
    NormalSquareTranslatedEdgeWindow e :=
  match d with
  | horizontal hEdge hMargins cover =>
      horizontalSquareLatticeEdgeWindow_of_margins e hEdge hMargins cover
  | vertical hEdge hMargins cover =>
      verticalSquareLatticeEdgeWindow_of_margins e hEdge hMargins cover

/-- The one-edge blocking datum obtained from oriented margin-and-cover data.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def blockingDatum
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {e : Edge (squareLatticeGraph width height)}
    (d : NormalSquareEdgeMarginCover e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height) e :=
  d.window.blockingDatum h hUnion

/-- Oriented margin-and-cover data supply the three injective regions for the
edge-blocked chain.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem injective_chain
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {e : Edge (squareLatticeGraph width height)}
    (d : NormalSquareEdgeMarginCover e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) :
    κ.IsInjective ((d.blockingDatum h hUnion).red) ∧
      κ.IsInjective ((d.blockingDatum h hUnion).blue) ∧
      κ.IsInjective ((d.blockingDatum h hUnion).complement) :=
  (d.blockingDatum h hUnion).injective_chain

/-- Oriented margin-and-cover data supply endpoint membership, pairwise
disjointness, and coverage by the three blocking regions.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem endpoint_disjoint_cover
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {e : Edge (squareLatticeGraph width height)}
    (d : NormalSquareEdgeMarginCover e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) :
    e.1.1 ∈ (d.blockingDatum h hUnion).red ∧
      e.1.2 ∈ (d.blockingDatum h hUnion).blue ∧
      Disjoint ((d.blockingDatum h hUnion).red) ((d.blockingDatum h hUnion).blue) ∧
      Disjoint ((d.blockingDatum h hUnion).red)
        ((d.blockingDatum h hUnion).complement) ∧
      Disjoint ((d.blockingDatum h hUnion).blue)
        ((d.blockingDatum h hUnion).complement) ∧
      (d.blockingDatum h hUnion).red ∪ (d.blockingDatum h hUnion).blue ∪
          (d.blockingDatum h hUnion).complement =
        (Finset.univ : Finset (SquareLatticeVertex width height)) :=
  (d.blockingDatum h hUnion).endpoint_disjoint_cover

end NormalSquareEdgeMarginCover

/-- A choice of translated edge window for every edge assembles into the normal
edge-blocking hypotheses.

This is the conditional construction preceding the finite \(7\times7\)
geometry argument: it assumes the translated window for each edge rather than
constructing those windows.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareTranslatedEdgeBlockingHypotheses_of_windows
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (windows :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareTranslatedEdgeWindow.{edgeCoverUniverse} e) :
    NormalEdgeBlockingHypotheses κ (squareLatticeGraph width height) :=
  NormalEdgeBlockingHypotheses.ofBlockingData fun e =>
    (windows e).blockingDatum h hUnion

/-- The edge datum recovered from the hypotheses assembled from translated
windows is the datum supplied by the chosen translated window at that edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareTranslatedEdgeBlockingHypotheses_blockingData_of_windows
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (windows :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareTranslatedEdgeWindow.{edgeCoverUniverse} e)
    (e : Edge (squareLatticeGraph width height)) :
    (normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion windows).blockingData e =
      (windows e).blockingDatum h hUnion := by
  rfl

/-- The edge-blocking hypotheses assembled from translated windows give the
three injective regions at every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareTranslatedEdgeBlockingHypotheses_injective_chain_of_windows
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (windows :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareTranslatedEdgeWindow.{edgeCoverUniverse} e)
    (e : Edge (squareLatticeGraph width height)) :
    κ.IsInjective ((normalSquareTranslatedEdgeBlockingHypotheses_of_windows
        h hUnion windows).red e) ∧
      κ.IsInjective ((normalSquareTranslatedEdgeBlockingHypotheses_of_windows
        h hUnion windows).blue e) ∧
      κ.IsInjective ((normalSquareTranslatedEdgeBlockingHypotheses_of_windows
        h hUnion windows).complement e) :=
  (normalSquareTranslatedEdgeBlockingHypotheses_of_windows
    h hUnion windows).injective_chain_at_edge e

/-- The edge-blocking hypotheses assembled from translated windows give
endpoint membership, pairwise disjointness, and coverage at every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareTranslatedEdgeBlockingHypotheses_endpoint_disjoint_cover_of_windows
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (windows :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareTranslatedEdgeWindow.{edgeCoverUniverse} e)
    (e : Edge (squareLatticeGraph width height)) :
    e.1.1 ∈ (normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion windows).red e ∧
      e.1.2 ∈ (normalSquareTranslatedEdgeBlockingHypotheses_of_windows
        h hUnion windows).blue e ∧
      Disjoint ((normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion windows).red e)
        ((normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion windows).blue e) ∧
      Disjoint ((normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion windows).red e)
        ((normalSquareTranslatedEdgeBlockingHypotheses_of_windows
          h hUnion windows).complement e) ∧
      Disjoint ((normalSquareTranslatedEdgeBlockingHypotheses_of_windows
          h hUnion windows).blue e)
        ((normalSquareTranslatedEdgeBlockingHypotheses_of_windows
          h hUnion windows).complement e) ∧
      (normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion windows).red e ∪
          (normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion windows).blue e ∪
            (normalSquareTranslatedEdgeBlockingHypotheses_of_windows
              h hUnion windows).complement e =
        (Finset.univ : Finset (SquareLatticeVertex width height)) :=
  let H := normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion windows
  H.endpoint_disjoint_cover_at_edge e

/-- A choice of oriented margin-and-cover data for every edge assembles into
the normal edge-blocking hypotheses.

This is the same conditional construction as
`normalSquareTranslatedEdgeBlockingHypotheses_of_windows`, with the per-edge
finite-geometry input expressed directly on each square-lattice edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareEdgeBlockingHypotheses_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e) :
    NormalEdgeBlockingHypotheses κ (squareLatticeGraph width height) :=
  normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion fun e =>
    (data e).window

/-- The edge datum recovered from the assembled hypotheses is the datum supplied
by the corresponding oriented margin-and-cover input.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareEdgeBlockingHypotheses_blockingData_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (e : Edge (squareLatticeGraph width height)) :
    (normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).blockingData e =
      (data e).blockingDatum h hUnion := by
  rfl

/-- The edge-blocking hypotheses assembled from oriented margin-and-cover data
give the three injective regions at every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareEdgeBlockingHypotheses_injective_chain_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (e : Edge (squareLatticeGraph width height)) :
    κ.IsInjective ((normalSquareEdgeBlockingHypotheses_of_marginCovers
        h hUnion data).red e) ∧
      κ.IsInjective ((normalSquareEdgeBlockingHypotheses_of_marginCovers
        h hUnion data).blue e) ∧
      κ.IsInjective ((normalSquareEdgeBlockingHypotheses_of_marginCovers
        h hUnion data).complement e) :=
  (normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).injective_chain_at_edge e

/-- The edge-blocking hypotheses assembled from oriented margin-and-cover data
give endpoint membership, pairwise disjointness, and coverage at every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareEdgeBlockingHypotheses_endpoint_disjoint_cover_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (e : Edge (squareLatticeGraph width height)) :
    e.1.1 ∈ (normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).red e ∧
      e.1.2 ∈ (normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).blue e ∧
      Disjoint ((normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).red e)
        ((normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).blue e) ∧
      Disjoint ((normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).red e)
        ((normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).complement e) ∧
      Disjoint ((normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).blue e)
        ((normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).complement e) ∧
      (normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).red e ∪
          (normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).blue e ∪
            (normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data).complement e =
        (Finset.univ : Finset (SquareLatticeVertex width height)) :=
  let H := normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data
  H.endpoint_disjoint_cover_at_edge e

end TNLean.PEPS
