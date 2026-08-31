/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NormalEdgeBlockingTranslated

/-!
# Margin constraints for translated normal edge blockings

This file records the coordinate margin consequences of the translated
edge-blocking criterion and the resulting open-boundary obstruction for the
present open rectangular square-lattice model.

The boundary nonexistence statements below concern this open-rectangle model.
They do not contradict the every-edge blocking sentence in arXiv:1804.04964.
The final section also gives an abstract region-injectivity countermodel: the
source rectangular hypotheses and union closure alone do not imply a
red/blue/complement blocking at a boundary edge. Thus an open-boundary
extension requires additional tensor-level or boundary injectivity input.
The comparison with the paper and the boundary obstruction are recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining
mathematical obligations".

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3]
-/

namespace TNLean
namespace PEPS

/-! ### Boundary obstructions for the present open-rectangle model -/

/-- A translated window on a coordinate right edge forces exactly the
horizontal margin inequalities used by the current interior window criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem normalSquareTranslatedEdgeWindow_rightEdge_margins
    {width height x y : ℕ} {hx : x + 1 < width} {hy : y < height}
    (w : NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := width) (height := height) x y hx hy)) :
    IsNormalSquareHorizontalEdgeMargins width height x y := by
  cases w with
  | horizontal xStart yStart hxw hyw edge_eq _cover =>
      have hxcoord : xStart + 1 = x := by
        have h :=
          congrArg
            (fun e : Edge (squareLatticeGraph width height) => e.1.1.1.1)
            edge_eq
        simpa [normalSquareHorizontalTranslatedEdge, squareLatticeRightEdge] using h
      have hycoord : yStart + 2 = y := by
        have h :=
          congrArg
            (fun e : Edge (squareLatticeGraph width height) => e.1.1.2.1)
            edge_eq
        simpa [normalSquareHorizontalTranslatedEdge, squareLatticeRightEdge] using h
      unfold IsNormalSquareHorizontalEdgeMargins
      omega
  | vertical xStart yStart _hxw _hyw edge_eq _cover =>
      have hVertical :
          IsVerticalSquareLatticeEdge
            (squareLatticeRightEdge (width := width) (height := height) x y hx hy) := by
        rw [← edge_eq]
        exact normalSquareVerticalTranslatedEdge_isVertical (by omega) (by omega)
      have hHorizontal :
          IsHorizontalSquareLatticeEdge
            (squareLatticeRightEdge (width := width) (height := height) x y hx hy) :=
        squareLatticeRightEdge_isHorizontal hx hy
      exact
        False.elim
          ((squareLatticeEdge_not_horizontal_and_vertical _
            ⟨hHorizontal, hVertical⟩))

/-- A translated window on a coordinate upward edge forces exactly the vertical
margin inequalities used by the current interior window criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem normalSquareTranslatedEdgeWindow_upEdge_margins
    {width height x y : ℕ} {hx : x < width} {hy : y + 1 < height}
    (w : NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := width) (height := height) x y hx hy)) :
    IsNormalSquareVerticalEdgeMargins width height x y := by
  cases w with
  | horizontal xStart yStart _hxw _hyw edge_eq _cover =>
      have hHorizontal :
          IsHorizontalSquareLatticeEdge
            (squareLatticeUpEdge (width := width) (height := height) x y hx hy) := by
        rw [← edge_eq]
        exact normalSquareHorizontalTranslatedEdge_isHorizontal (by omega) (by omega)
      have hVertical :
          IsVerticalSquareLatticeEdge
            (squareLatticeUpEdge (width := width) (height := height) x y hx hy) :=
        squareLatticeUpEdge_isVertical hx hy
      exact
        False.elim
          ((squareLatticeEdge_not_horizontal_and_vertical _
            ⟨hHorizontal, hVertical⟩))
  | vertical xStart yStart hxw hyw edge_eq _cover =>
      have hxcoord : xStart + 2 = x := by
        have h :=
          congrArg
            (fun e : Edge (squareLatticeGraph width height) => e.1.1.1.1)
            edge_eq
        simpa [normalSquareVerticalTranslatedEdge, squareLatticeUpEdge] using h
      have hycoord : yStart + 1 = y := by
        have h :=
          congrArg
            (fun e : Edge (squareLatticeGraph width height) => e.1.1.2.1)
            edge_eq
        simpa [normalSquareVerticalTranslatedEdge, squareLatticeUpEdge] using h
      unfold IsNormalSquareVerticalEdgeMargins
      omega

/-- In the current open rectangular coordinate graph, a left-boundary right
edge does not admit a translated edge window.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_leftBoundaryRightEdge_window {width height y : ℕ}
    (hx : 0 + 1 < width) (hy : y < height) :
    ¬ Nonempty (NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := width) (height := height) 0 y hx hy)) := by
  rintro ⟨w⟩
  exact Nat.not_succ_le_zero 0 (normalSquareTranslatedEdgeWindow_rightEdge_margins w).1

/-- In the current open \(7\times7\) rectangular coordinate graph, the left
boundary right edge at height \(2\) does not admit a translated edge window.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_leftBoundaryRightEdge_window_seven :
    ¬ Nonempty (NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := 7) (height := 7) 0 2
        (by decide) (by decide))) := by
  exact not_leftBoundaryRightEdge_window (by decide) (by decide)

/-- In the current open rectangular coordinate graph, a right edge too close
to the right side does not admit a translated edge window.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_rightMarginRightEdge_window {width height x y : ℕ}
    (hx : x + 1 < width) (hy : y < height) (hRight : ¬ x + 4 ≤ width) :
    ¬ Nonempty (NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := width) (height := height) x y hx hy)) := by
  rintro ⟨w⟩
  exact hRight (normalSquareTranslatedEdgeWindow_rightEdge_margins w).2.1

/-- In the current open \(7\times7\) rectangular coordinate graph, the right
edge at horizontal coordinate \(5\) and height \(2\) does not admit a
translated edge window.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_rightMarginRightEdge_window_seven :
    ¬ Nonempty (NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := 7) (height := 7) 5 2
        (by decide) (by decide))) := by
  exact not_rightMarginRightEdge_window (by decide) (by decide) (by decide)

/-- In the current open rectangular coordinate graph, a bottom-boundary upward
edge does not admit a translated edge window.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_bottomBoundaryUpEdge_window {width height x : ℕ}
    (hx : x < width) (hy : 0 + 1 < height) :
    ¬ Nonempty (NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := width) (height := height) x 0 hx hy)) := by
  rintro ⟨w⟩
  exact Nat.not_succ_le_zero 0 (normalSquareTranslatedEdgeWindow_upEdge_margins w).2.2.1

/-- In the current open \(7\times7\) rectangular coordinate graph, the bottom
boundary upward edge at horizontal coordinate \(2\) does not admit a translated
edge window.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_bottomBoundaryUpEdge_window_seven :
    ¬ Nonempty (NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := 7) (height := 7) 2 0
        (by decide) (by decide))) := by
  exact not_bottomBoundaryUpEdge_window (by decide) (by decide)

/-- In the current open rectangular coordinate graph, an upward edge too close
to the top side does not admit a translated edge window.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_topMarginUpEdge_window {width height x y : ℕ}
    (hx : x < width) (hy : y + 1 < height) (hTop : ¬ y + 4 ≤ height) :
    ¬ Nonempty (NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := width) (height := height) x y hx hy)) := by
  rintro ⟨w⟩
  exact hTop (normalSquareTranslatedEdgeWindow_upEdge_margins w).2.2.2

/-- In the current open \(7\times7\) rectangular coordinate graph, the upward
edge at horizontal coordinate \(2\) and height \(5\) does not admit a
translated edge window.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_topMarginUpEdge_window_seven :
    ¬ Nonempty (NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := 7) (height := 7) 2 5
        (by decide) (by decide))) := by
  exact not_topMarginUpEdge_window (by decide) (by decide) (by decide)

/-- The current open \(7\times7\) rectangular coordinate graph has explicit
horizontal and vertical boundary edges on all four sides that do not admit
translated edge windows.

This records a four-sided obstruction for the present translated-window
criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_fourSidedBoundaryWindow_seven :
    (¬ Nonempty (NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := 7) (height := 7) 0 2
        (by decide) (by decide)))) ∧
      (¬ Nonempty (NormalSquareTranslatedEdgeWindow
        (squareLatticeRightEdge (width := 7) (height := 7) 5 2
          (by decide) (by decide)))) ∧
      (¬ Nonempty (NormalSquareTranslatedEdgeWindow
        (squareLatticeUpEdge (width := 7) (height := 7) 2 0
          (by decide) (by decide)))) ∧
      (¬ Nonempty (NormalSquareTranslatedEdgeWindow
        (squareLatticeUpEdge (width := 7) (height := 7) 2 5
          (by decide) (by decide)))) := by
  exact
    ⟨not_leftBoundaryRightEdge_window_seven,
      not_rightMarginRightEdge_window_seven,
      not_bottomBoundaryUpEdge_window_seven,
      not_topMarginUpEdge_window_seven⟩

/-- The current open \(7\times7\) rectangular coordinate graph does not admit
a family of translated edge windows over all edges.

This records that the present translated-window criterion is an interior
sufficient criterion; the boundary geometry still has to be supplied
separately.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_forall_normalSquareTranslatedEdgeWindow_seven :
    ¬ Nonempty (∀ e : Edge (squareLatticeGraph 7 7),
      NormalSquareTranslatedEdgeWindow e) := by
  rintro ⟨windows⟩
  exact not_leftBoundaryRightEdge_window (by decide) (by decide)
    ⟨windows (squareLatticeRightEdge (width := 7) (height := 7) 0 2
      (by decide) (by decide))⟩

/-- A translated margin-cover datum on a coordinate right edge forces exactly
the horizontal margin inequalities used by the current interior criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem normalSquareEdgeMarginCover_rightEdge_bounds
    {width height x y : ℕ} {hx : x + 1 < width} {hy : y < height}
    (d : NormalSquareEdgeMarginCover
      (squareLatticeRightEdge (width := width) (height := height) x y hx hy)) :
    IsNormalSquareHorizontalEdgeMargins width height x y := by
  cases d with
  | horizontal _hEdge hMargins _cover =>
      simpa [IsNormalSquareHorizontalEdgeMargins, squareLatticeRightEdge] using hMargins
  | vertical hEdge _hMargins _cover =>
      have hHorizontal :
          IsHorizontalSquareLatticeEdge
            (squareLatticeRightEdge (width := width) (height := height) x y hx hy) :=
        squareLatticeRightEdge_isHorizontal hx hy
      exact
        False.elim
          ((squareLatticeEdge_not_horizontal_and_vertical
            (squareLatticeRightEdge (width := width) (height := height) x y hx hy)
            ⟨hHorizontal, hEdge⟩))

/-- A translated margin-cover datum on a coordinate upward edge forces exactly
the vertical margin inequalities used by the current interior criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem normalSquareEdgeMarginCover_upEdge_bounds
    {width height x y : ℕ} {hx : x < width} {hy : y + 1 < height}
    (d : NormalSquareEdgeMarginCover
      (squareLatticeUpEdge (width := width) (height := height) x y hx hy)) :
    IsNormalSquareVerticalEdgeMargins width height x y := by
  cases d with
  | horizontal hEdge _hMargins _cover =>
      have hVertical :
          IsVerticalSquareLatticeEdge
            (squareLatticeUpEdge (width := width) (height := height) x y hx hy) :=
        squareLatticeUpEdge_isVertical hx hy
      exact
        False.elim
          ((squareLatticeEdge_not_horizontal_and_vertical
            (squareLatticeUpEdge (width := width) (height := height) x y hx hy)
            ⟨hEdge, hVertical⟩))
  | vertical _hEdge hMargins _cover =>
      simpa [IsNormalSquareVerticalEdgeMargins, squareLatticeUpEdge] using hMargins

/-- In the current open rectangular coordinate graph, a left-boundary right
edge does not satisfy the translated horizontal margin criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_leftBoundaryRightEdge_marginCover {width height y : ℕ}
    (hx : 0 + 1 < width) (hy : y < height) :
    ¬ Nonempty (NormalSquareEdgeMarginCover
      (squareLatticeRightEdge (width := width) (height := height) 0 y hx hy)) := by
  rintro ⟨d⟩
  exact Nat.not_succ_le_zero 0 (normalSquareEdgeMarginCover_rightEdge_bounds d).1

/-- In the current open \(7\times7\) rectangular coordinate graph, the left
boundary right edge at height \(2\) does not satisfy the translated horizontal
margin criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_leftBoundaryRightEdge_marginCover_seven :
    ¬ Nonempty (NormalSquareEdgeMarginCover
      (squareLatticeRightEdge (width := 7) (height := 7) 0 2
        (by decide) (by decide))) := by
  exact not_leftBoundaryRightEdge_marginCover (by decide) (by decide)

/-- In the current open rectangular coordinate graph, a right edge too close
to the right side does not satisfy the translated horizontal margin criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_rightMarginRightEdge_marginCover {width height x y : ℕ}
    (hx : x + 1 < width) (hy : y < height) (hRight : ¬ x + 4 ≤ width) :
    ¬ Nonempty (NormalSquareEdgeMarginCover
      (squareLatticeRightEdge (width := width) (height := height) x y hx hy)) := by
  rintro ⟨d⟩
  exact hRight (normalSquareEdgeMarginCover_rightEdge_bounds d).2.1

/-- In the current open \(7\times7\) rectangular coordinate graph, the right
edge at horizontal coordinate \(5\) and height \(2\) does not satisfy the
translated horizontal margin criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_rightMarginRightEdge_marginCover_seven :
    ¬ Nonempty (NormalSquareEdgeMarginCover
      (squareLatticeRightEdge (width := 7) (height := 7) 5 2
        (by decide) (by decide))) := by
  exact not_rightMarginRightEdge_marginCover (by decide) (by decide) (by decide)

/-- In the current open rectangular coordinate graph, a bottom-boundary upward
edge does not satisfy the translated vertical margin criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_bottomBoundaryUpEdge_marginCover {width height x : ℕ}
    (hx : x < width) (hy : 0 + 1 < height) :
    ¬ Nonempty (NormalSquareEdgeMarginCover
      (squareLatticeUpEdge (width := width) (height := height) x 0 hx hy)) := by
  rintro ⟨d⟩
  exact Nat.not_succ_le_zero 0 (normalSquareEdgeMarginCover_upEdge_bounds d).2.2.1

/-- In the current open \(7\times7\) rectangular coordinate graph, the bottom
boundary upward edge at horizontal coordinate \(2\) does not satisfy the
translated vertical margin criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_bottomBoundaryUpEdge_marginCover_seven :
    ¬ Nonempty (NormalSquareEdgeMarginCover
      (squareLatticeUpEdge (width := 7) (height := 7) 2 0
        (by decide) (by decide))) := by
  exact not_bottomBoundaryUpEdge_marginCover (by decide) (by decide)

/-- In the current open rectangular coordinate graph, an upward edge too close
to the top side does not satisfy the translated vertical margin criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_topMarginUpEdge_marginCover {width height x y : ℕ}
    (hx : x < width) (hy : y + 1 < height) (hTop : ¬ y + 4 ≤ height) :
    ¬ Nonempty (NormalSquareEdgeMarginCover
      (squareLatticeUpEdge (width := width) (height := height) x y hx hy)) := by
  rintro ⟨d⟩
  exact hTop (normalSquareEdgeMarginCover_upEdge_bounds d).2.2.2

/-- In the current open \(7\times7\) rectangular coordinate graph, the upward
edge at horizontal coordinate \(2\) and height \(5\) does not satisfy the
translated vertical margin criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_topMarginUpEdge_marginCover_seven :
    ¬ Nonempty (NormalSquareEdgeMarginCover
      (squareLatticeUpEdge (width := 7) (height := 7) 2 5
        (by decide) (by decide))) := by
  exact not_topMarginUpEdge_marginCover (by decide) (by decide) (by decide)

/-- The current open \(7\times7\) rectangular coordinate graph has explicit
horizontal and vertical boundary edges on all four sides that do not satisfy
the translated margin-cover criterion.

This records a four-sided obstruction for the present margin criterion.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_fourSidedBoundaryMarginCover_seven :
    (¬ Nonempty (NormalSquareEdgeMarginCover
      (squareLatticeRightEdge (width := 7) (height := 7) 0 2
        (by decide) (by decide)))) ∧
      (¬ Nonempty (NormalSquareEdgeMarginCover
        (squareLatticeRightEdge (width := 7) (height := 7) 5 2
          (by decide) (by decide)))) ∧
      (¬ Nonempty (NormalSquareEdgeMarginCover
        (squareLatticeUpEdge (width := 7) (height := 7) 2 0
          (by decide) (by decide)))) ∧
      (¬ Nonempty (NormalSquareEdgeMarginCover
        (squareLatticeUpEdge (width := 7) (height := 7) 2 5
          (by decide) (by decide)))) := by
  exact
    ⟨not_leftBoundaryRightEdge_marginCover_seven,
      not_rightMarginRightEdge_marginCover_seven,
      not_bottomBoundaryUpEdge_marginCover_seven,
      not_topMarginUpEdge_marginCover_seven⟩

/-- The current open \(7\times7\) rectangular coordinate graph does not admit
a family of translated margin-cover data over all edges.

This records that the present margin criterion is an interior sufficient
criterion; the boundary geometry still has to be supplied separately.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500. -/
theorem not_forall_normalSquareEdgeMarginCover_seven :
    ¬ Nonempty (∀ e : Edge (squareLatticeGraph 7 7),
      NormalSquareEdgeMarginCover e) := by
  rintro ⟨data⟩
  exact not_leftBoundaryRightEdge_marginCover_seven
    ⟨data (squareLatticeRightEdge (width := 7) (height := 7) 0 2
      (by decide) (by decide))⟩

/-! ### Rectangular injectivity does not force an open-boundary blocking -/

/-- An abstract region-injectivity predicate used to test the left boundary
edge of the open \(7\times7\) rectangle.

A region is declared injective only if containing the left endpoint of the
chosen boundary edge forces it to contain the right endpoint. This predicate
is not asserted to arise from a PEPS tensor. It is a countermodel internal to
the abstract `RegionInjectivityData` interface.

Source comparison: arXiv:1804.04964, Theorem `normal`, lines 1574--1585,
assumes an injective three-part blocking around every edge; it does not derive
that hypothesis from rectangular injectivity on an open rectangle. -/
def leftBoundaryRightEdgeInjectivityCountermodelSeven :
    RegionInjectivityData (SquareLatticeVertex 7 7) where
  IsInjective R :=
    (squareLatticeRightEdge (width := 7) (height := 7) 0 2
      (by decide) (by decide)).1.1 ∈ R →
      (squareLatticeRightEdge (width := 7) (height := 7) 0 2
        (by decide) (by decide)).1.2 ∈ R

/-- The boundary-edge countermodel is closed under unions of injective
regions, as required by the union lemma of the source.

Source comparison: arXiv:1804.04964, Lemma `injective_union`, lines
1322--1404. -/
theorem leftBoundaryRightEdgeInjectivityCountermodelSeven_unionClosure :
    RegionInjectivityUnionClosure leftBoundaryRightEdgeInjectivityCountermodelSeven := by
  constructor
  intro A B hA hB hLeft
  rw [Finset.mem_union] at hLeft ⊢
  exact hLeft.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h))

/-- Every contiguous \(2\times3\) and \(3\times2\) rectangle in the open
\(7\times7\) lattice is injective for the boundary-edge countermodel.

Indeed, any such rectangle containing the left endpoint at horizontal
coordinate zero also contains its right neighbor.

Source comparison: arXiv:1804.04964, Theorem 3, lines 1407--1452. -/
theorem leftBoundaryRightEdgeInjectivityCountermodelSeven_rectangular :
    NormalSquareLatticeRectangleInjectivityHypotheses
      leftBoundaryRightEdgeInjectivityCountermodelSeven := by
  constructor
  · intro R hR
    obtain ⟨xStart, yStart, _hx, _hy, rfl⟩ := hR
    intro hLeft
    rw [mem_squareLatticeContiguousRectangle] at hLeft ⊢
    simp only [squareLatticeRightEdge] at hLeft ⊢
    omega
  · intro R hR
    obtain ⟨xStart, yStart, _hx, _hy, rfl⟩ := hR
    intro hLeft
    rw [mem_squareLatticeContiguousRectangle] at hLeft ⊢
    simp only [squareLatticeRightEdge] at hLeft ⊢
    omega

/-- The countermodel admits no red/blue/complement blocking datum at the
chosen left-boundary edge.

The red block contains the left endpoint. Its countermodel injectivity then
places the right endpoint in the red block, contradicting its required
membership in the disjoint blue block.

This is an obstruction only to deriving the open-boundary blocking from the
abstract rectangular-injectivity and union-closure hypotheses. It does not
concern the periodic translationally invariant statement of arXiv:1804.04964,
Theorem 3.

Source comparison: arXiv:1804.04964, Theorem `normal`, lines 1574--1585. -/
theorem not_leftBoundaryRightEdge_blockingData_countermodelSeven :
    ¬ Nonempty
      (NormalEdgeBlockingData leftBoundaryRightEdgeInjectivityCountermodelSeven
        (squareLatticeGraph 7 7)
        (squareLatticeRightEdge (width := 7) (height := 7) 0 2
          (by decide) (by decide))) := by
  rintro ⟨d⟩
  have hRightRed := d.red_injective d.left_mem_red
  exact Finset.disjoint_left.mp d.red_disjoint_blue hRightRed d.right_mem_blue

/-- Rectangular injectivity and union closure alone do not imply an
open-boundary blocking datum in the abstract region-injectivity interface.

The witness is the left-boundary countermodel on the open \(7\times7\)
rectangle. Thus a theorem constructing boundary-near
`NormalEdgeBlockingData` requires additional tensor-level or boundary
injectivity input; it cannot follow from the two abstract hypotheses used by
the interior tiling argument alone.

Source comparison: arXiv:1804.04964, Theorem `normal`, lines 1574--1585,
takes the every-edge injective blocking as a hypothesis. -/
theorem exists_rectangularInjectivity_not_boundaryBlockingData :
    ∃ κ : RegionInjectivityData (SquareLatticeVertex 7 7),
      NormalSquareLatticeRectangleInjectivityHypotheses κ ∧
        RegionInjectivityUnionClosure κ ∧
          ¬ Nonempty
            (NormalEdgeBlockingData κ (squareLatticeGraph 7 7)
              (squareLatticeRightEdge (width := 7) (height := 7) 0 2
                (by decide) (by decide))) :=
  ⟨leftBoundaryRightEdgeInjectivityCountermodelSeven,
    leftBoundaryRightEdgeInjectivityCountermodelSeven_rectangular,
    leftBoundaryRightEdgeInjectivityCountermodelSeven_unionClosure,
    not_leftBoundaryRightEdge_blockingData_countermodelSeven⟩

end PEPS
end TNLean
