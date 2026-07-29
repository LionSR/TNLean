/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCoordinateSwap
import TNLean.PEPS.TorusWindowFamily

/-!
# The staircase window family around a vertical edge

The vertical staircase is the image of the horizontal staircase under coordinate
interchange, with the side lengths exchanged.  This module keeps the public
vertical family of declarations while deriving its geometry from
`TorusWindowFamily` through `torusCoordinateSwapRegion`.

In staircase coordinates `s = (a, b)`, the resulting windows are the cyclic
`L × K` rectangles

* `W_j = [a + L - 1, a + 2L - 1) × [b + K - j, b + 2K - j)` for `j ≤ K`;
* `W_{K+i} = [a + L - 1 - i, a + 2L - 1 - i) × [b, b + K)`.

The first arm descends and the second shifts horizontally.  What is recorded
below is the vertical family itself together with the two rectangle identities
for its union: the union of the first `K` windows is the cyclic vertical
rectangle, and the union of the remaining windows is the cyclic horizontal one.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
* `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section on the window
  family around an edge.
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-! ### Transported end windows, patch, and family -/

/-- The first vertical end window, obtained by transposing the first horizontal
end window with exchanged side lengths. -/
def verticalStaircaseRightWindow (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusCoordinateSwapRegion (horizontalStaircaseRightWindow (s.2, s.1) K L)

/-- The last vertical end window, obtained by transposing the last horizontal
end window with exchanged side lengths. -/
def verticalStaircaseLeftWindow (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusCoordinateSwapRegion (horizontalStaircaseLeftWindow (s.2, s.1) K L)

/-- The vertical staircase patch is the transpose of the horizontal patch with
exchanged side lengths. -/
def verticalStaircasePatch (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusCoordinateSwapRegion (horizontalStaircasePatch (s.2, s.1) K L)

/-- The `j`-th vertical staircase window is the transpose of the `j`-th
horizontal staircase window with exchanged side lengths. -/
def verticalStaircaseWindow (s : TorusVertex width height) (L K j : ℕ) :
    Finset (TorusVertex width height) :=
  torusCoordinateSwapRegion (staircaseWindow (s.2, s.1) K L j)

/-! ### Transported consecutive-window unions -/

/-- The union of two consecutive vertical staircase windows, defined as the
coordinate transpose of the corresponding horizontal union. -/
def verticalStaircaseUnion (s : TorusVertex width height) (L K j : ℕ) :
    Finset (TorusVertex width height) :=
  torusCoordinateSwapRegion (staircaseUnion (s.2, s.1) K L j)

/-- A descending-arm consecutive union is an `L × (K + 1)` cyclic rectangle. -/
theorem verticalStaircaseUnion_eq_verticalRectangle {L K : ℕ} (hh : 1 < height)
    (s : TorusVertex width height) {j : ℕ} (hj : j < K) :
    verticalStaircaseUnion s L K j =
      torusArcRectangle
        (s.1 + ((L - 1 : ℕ) : ZMod width), s.2 + ((K - (j + 1) : ℕ) : ZMod height))
        L (K + 1) := by
  have h := congrArg torusCoordinateSwapRegion
    (staircaseUnion_eq_horizontalRectangle (width := height) (height := width)
      (L := K) (K := L) hh (s.2, s.1) hj)
  simpa only [verticalStaircaseUnion,
    torusCoordinateSwapRegion_torusArcRectangle] using h

/-- A right-shifting-arm consecutive union is an `(L + 1) × K` cyclic rectangle. -/
theorem verticalStaircaseUnion_eq_horizontalRectangle {L K : ℕ} (hw : 1 < width)
    (s : TorusVertex width height) {j : ℕ} (hj : K ≤ j) (hjK : j + 1 < L + K) :
    verticalStaircaseUnion s L K j =
      torusArcRectangle
        (s.1 + ((L - 1 - ((j + 1) - K) : ℕ) : ZMod width), s.2) (L + 1) K := by
  have h := congrArg torusCoordinateSwapRegion
    (staircaseUnion_eq_verticalRectangle (width := height) (height := width)
      (L := K) (K := L) hw (s.2, s.1) hj (by simpa [Nat.add_comm] using hjK))
  simpa only [verticalStaircaseUnion,
    torusCoordinateSwapRegion_torusArcRectangle] using h

end PEPS
end TNLean
