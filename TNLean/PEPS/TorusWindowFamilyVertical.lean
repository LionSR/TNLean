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

The first arm descends and the second shifts horizontally.  A union of two
consecutive windows is again a cyclic rectangle: on the descending arm, where
`j < K`, it is `L × (K + 1)`, and on the shifting arm, where `K ≤ j` and
`j + 1 < L + K`, it is `(L + 1) × K`.

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

/-- The first window of the vertical family is its first end window. -/
@[deprecated "Expand `verticalStaircaseWindow` and use `staircaseWindow_zero`."
  (since := "2026-07-30")]
theorem verticalStaircaseWindow_zero (s : TorusVertex width height) (L K : ℕ) :
    verticalStaircaseWindow s L K 0 = verticalStaircaseRightWindow s L K := by
  simp only [verticalStaircaseWindow, verticalStaircaseRightWindow, staircaseWindow_zero]

/-- The last window of the vertical family is its last end window. -/
@[deprecated "Expand the vertical-window definitions and use `staircaseWindow_last`."
  (since := "2026-07-30")]
theorem verticalStaircaseWindow_last (s : TorusVertex width height) {L K : ℕ}
    (hL : 0 < L) (hK : 0 < K) :
    verticalStaircaseWindow s L K (L + K - 1) = verticalStaircaseLeftWindow s L K := by
  rw [verticalStaircaseWindow, verticalStaircaseLeftWindow, Nat.add_comm,
    staircaseWindow_last (s.2, s.1) hK hL]

/-- Every vertical staircase window is an `L × K` cyclic window, hence is
injective under the window hypotheses. -/
@[deprecated "Expand `verticalStaircaseWindow` and apply `arcWindow_injective`."
  (since := "2026-07-30")]
theorem NormalTorusArcWindowInjectivityHypotheses.verticalStaircaseWindow_injective
    {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (s : TorusVertex width height) (j : ℕ) :
    κ.IsInjective (verticalStaircaseWindow s L K j) := by
  rw [verticalStaircaseWindow, staircaseWindow,
    torusCoordinateSwapRegion_torusArcRectangle]
  exact h.arcWindow_injective _

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

/-- Each vertical consecutive union is injective under the window and union
closure hypotheses. -/
@[deprecated "Rewrite with `verticalStaircaseUnion_eq_verticalRectangle` or
`verticalStaircaseUnion_eq_horizontalRectangle`, then use the corresponding union
injectivity theorem." (since := "2026-07-30")]
theorem NormalTorusArcWindowInjectivityHypotheses.verticalStaircaseUnion_injective
    {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) (s : TorusVertex width height)
    {j : ℕ} (hjK : j + 1 < L + K) :
    κ.IsInjective (verticalStaircaseUnion s L K j) := by
  by_cases hj : j < K
  · rw [verticalStaircaseUnion_eq_verticalRectangle (by omega) s hj]
    exact h.verticalUnion_injective hUnion hL hK hxw hyh _
  · rw [verticalStaircaseUnion_eq_horizontalRectangle (by omega) s (by omega) hjK]
    exact h.horizontalUnion_injective hUnion hL hK hxw hyh _

/-! ### Membership and transported nesting -/

/-- Membership in a vertical staircase window, expressed by cyclic distances
from the staircase corner. -/
@[deprecated "Expand `verticalStaircaseWindow` and use `mem_staircaseWindow`."
  (since := "2026-07-30")]
theorem mem_verticalStaircaseWindow {L K j : ℕ} (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (s : TorusVertex width height) (v : TorusVertex width height) :
    v ∈ verticalStaircaseWindow s L K j ↔
      ((L - 1 - (j - K) : ℕ) ≤ (v.1 - s.1).val ∧
          (v.1 - s.1).val < (L - 1 - (j - K)) + L) ∧
        ((K - j : ℕ) ≤ (v.2 - s.2).val ∧ (v.2 - s.2).val < (K - j) + K) := by
  rw [verticalStaircaseWindow, mem_torusCoordinateSwapRegion,
    mem_staircaseWindow hyh hxw]
  exact and_comm

/-- The first window of a consecutive vertical union sits in that union. -/
@[deprecated "Expand the vertical definitions and use
`staircaseWindow_subset_staircaseUnion`." (since := "2026-07-30")]
theorem verticalStaircaseWindow_subset_verticalStaircaseUnion
    (s : TorusVertex width height) (L K j : ℕ) :
    verticalStaircaseWindow s L K j ⊆ verticalStaircaseUnion s L K j :=
  torusCoordinateSwapRegion_mono (staircaseWindow_subset_staircaseUnion (s.2, s.1) K L j)

/-- The second window of a consecutive vertical union sits in that union. -/
@[deprecated "Expand the vertical definitions and use
`staircaseWindow_succ_subset_staircaseUnion`." (since := "2026-07-30")]
theorem verticalStaircaseWindow_succ_subset_verticalStaircaseUnion
    (s : TorusVertex width height) (L K j : ℕ) :
    verticalStaircaseWindow s L K (j + 1) ⊆ verticalStaircaseUnion s L K j :=
  torusCoordinateSwapRegion_mono
    (staircaseWindow_succ_subset_staircaseUnion (s.2, s.1) K L j)

/-- Each vertical staircase window sits in the transported staircase patch. -/
@[deprecated "Expand the vertical definitions and use `staircaseWindow_subset_patch`."
  (since := "2026-07-30")]
theorem verticalStaircaseWindow_subset_patch {L K j : ℕ} (hL : 0 < L)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    verticalStaircaseWindow s L K j ⊆ verticalStaircasePatch s L K :=
  torusCoordinateSwapRegion_mono
    (staircaseWindow_subset_patch hL hyh hxw (s.2, s.1))

/-- Each vertical consecutive union sits in the transported staircase patch. -/
@[deprecated "Expand the vertical definitions and use `staircaseUnion_subset_patch`."
  (since := "2026-07-30")]
theorem verticalStaircaseUnion_subset_patch {L K j : ℕ} (hL : 0 < L)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    verticalStaircaseUnion s L K j ⊆ verticalStaircasePatch s L K :=
  torusCoordinateSwapRegion_mono
    (staircaseUnion_subset_patch hL hyh hxw (s.2, s.1))

/-- The transported patch is exactly the union of the vertical staircase family. -/
@[deprecated "Expand the vertical definitions and use `biUnion_staircaseWindow_eq_patch`."
  (since := "2026-07-30")]
theorem biUnion_verticalStaircaseWindow_eq_patch {L K : ℕ} (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    (Finset.range (L + K)).biUnion (verticalStaircaseWindow s L K) =
      verticalStaircasePatch s L K := by
  calc
    (Finset.range (L + K)).biUnion (verticalStaircaseWindow s L K) =
        (Finset.range (K + L)).biUnion
          (fun j => torusCoordinateSwapRegion (staircaseWindow (s.2, s.1) K L j)) := by
      rw [Nat.add_comm]
      rfl
    _ = torusCoordinateSwapRegion
        ((Finset.range (K + L)).biUnion (staircaseWindow (s.2, s.1) K L)) :=
      (torusCoordinateSwapRegion_biUnion _ _).symm
    _ = torusCoordinateSwapRegion (horizontalStaircasePatch (s.2, s.1) K L) := by
      rw [biUnion_staircaseWindow_eq_patch hK hL hyh hxw]
    _ = verticalStaircasePatch s L K := rfl

end PEPS
end TNLean
