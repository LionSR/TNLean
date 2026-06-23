import TNLean.PEPS.TorusWindowChain

/-!
# The staircase window family around a vertical edge

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) compares, around a vertical edge, a family of
`L + K` overlapping windows that turn the corner of the edge: the first `K + 1`
descend across the edge one row at a time, then the last `L - 1` shift right one
column at a time.  This is the column--row transpose of the horizontal-edge family
of `TNLean/PEPS/TorusWindowFamily.lean`, with the roles of `L` and `K` and of the
two coordinate axes interchanged throughout.  This file builds the full indexed
family `W_0, …, W_{L+K-1}` interpolating between the two end windows, the
consecutive-window unions `U_j = W_j ∪ W_{j+1}`, and the subset nesting
`W_j ⊆ U_j ⊆ P` the open-boundary patch chaining consumes.  It is scoped in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section on the window family
around an edge.

## The family in staircase coordinates

In the staircase coordinates `s = (a, b)` of the end pair the windows are the cyclic
`L × K` rectangles

* `W_j = [a + L - 1, a + 2L - 1) × [b + K - j, b + 2K - j)` for `j = 0, …, K`, the
  descending arm sharing the column band `[a + L - 1, a + 2L - 1)`;
* `W_{K + i} = [a + L - 1 - i, a + 2L - 1 - i) × [b, b + K)` for `i = 1, …, L - 1`,
  the right-shifting arm sharing the row band `[b, b + K)`.

The corner window `W_K = [a + L - 1, a + 2L - 1) × [b, b + K)` is the meeting point of
the two arms.  The first window `W_0` is the right end window
`verticalStaircaseRightWindow` and the last `W_{L+K-1}` is the left end window
`verticalStaircaseLeftWindow`.  The offsets are read with truncated subtraction: the
row offset `K - j` collapses to `0` on the right-shifting arm and the column offset
`(L - 1) - (j - K)` collapses to `L - 1` on the descending arm, so a single formula
covers both arms with the corner window `W_K` shared.

## The consecutive-window unions

Two consecutive descending windows (`j < K`) differ by one row, so their union is the
`L × (K + 1)` cyclic rectangle of `verticalAdjacentWindows_union`.  Two consecutive
right-shifting windows (`K ≤ j`) differ by one column, so their union is the
`(L + 1) × K` cyclic rectangle of `horizontalAdjacentWindows_union`.  The transition
between the two arms is not a separate shape: the corner window `W_K` shares the row
band `[b, b + K)` with its successor `W_{K+1}`, so the union `U_K` is an ordinary
horizontal `(L + 1) × K` rectangle and the union `U_{K-1}` an ordinary vertical
`L × (K + 1)` rectangle.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and
  proof sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the
  section on the window family around an edge.
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-! ### The end windows and the patch around a vertical edge

The column--row transpose of the horizontal end windows and patch of
`TNLean/PEPS/TorusWindowChain.lean`.  The descending arm sweeps the `L × 2K` vertical
band `[a + L - 1, a + 2L - 1) × [b, b + 2K)`; the right-shifting arm sweeps the
`(2L - 1) × K` horizontal band `[a, a + 2L - 1) × [b, b + K)`. -/

/-- The right/first end window `W_0 = [a + L - 1, a + 2L - 1) × [b + K, b + 2K)` of the
vertical staircase, in the staircase coordinates `s = (a, b)`.

Source: arXiv:1804.04964, the corollary and proof sketch at lines 2297--2445 of
`Papers/1804.04964/paper_normal.tex` (the window family around the edge);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section on the window family. -/
def verticalStaircaseRightWindow (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle (s.1 + ((L - 1 : ℕ) : ZMod width), s.2 + (K : ZMod height)) L K

/-- The left/last end window `W_{L+K-1} = [a, a + L) × [b, b + K)` of the vertical
staircase, in the staircase coordinates `s = (a, b)`.

Source: arXiv:1804.04964, the corollary and proof sketch at lines 2297--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
the section on the window family. -/
def verticalStaircaseLeftWindow (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle s L K

/-- The vertical staircase patch `P`: the union of the `L × 2K` vertical band
`[a + L - 1, a + 2L - 1) × [b, b + 2K)` and the `(2L - 1) × K` horizontal band
`[a, a + 2L - 1) × [b, b + K)`, in the staircase coordinates `s = (a, b)`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the patch `P = ⋃_j W_j`);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section on the window family. -/
def verticalStaircasePatch (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle (s.1 + ((L - 1 : ℕ) : ZMod width), s.2) L (2 * K) ∪
    torusArcRectangle s (2 * L - 1) K

/-! ### The staircase window family -/

/-- The `j`-th window of the vertical staircase family around an edge, in the staircase
coordinates `s = (a, b)` of the end pair.  It is the cyclic `L × K` rectangle with
column start offset `(L - 1) - (j - K)` (truncated, so `L - 1` on the descending arm
`j ≤ K`) and row start offset `K - j` (truncated, so `0` on the right-shifting arm
`K ≤ j`):

* `W_j = [a + L - 1, a + 2L - 1) × [b + K - j, b + 2K - j)` for `j ≤ K`;
* `W_{K+i} = [a + L - 1 - i, a + 2L - 1 - i) × [b, b + K)` for `j = K + i`.

The shared corner window `W_K = [a + L - 1, a + 2L - 1) × [b, b + K)` sits at the
meeting of the two arms.  This is the column--row transpose of `staircaseWindow`.

Source: arXiv:1804.04964, the corollary and proof sketch at lines 2297--2445 of
`Papers/1804.04964/paper_normal.tex` (the window family around the edge);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section on the window family. -/
def verticalStaircaseWindow (s : TorusVertex width height) (L K j : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle
    (s.1 + ((L - 1 - (j - K) : ℕ) : ZMod width), s.2 + ((K - j : ℕ) : ZMod height)) L K

/-- The first window of the family is the right end window: at `j = 0` the column
offset is `L - 1` and the row offset `K`, the start of `verticalStaircaseRightWindow`. -/
theorem verticalStaircaseWindow_zero (s : TorusVertex width height) (L K : ℕ) :
    verticalStaircaseWindow s L K 0 = verticalStaircaseRightWindow s L K := by
  rw [verticalStaircaseWindow, verticalStaircaseRightWindow]
  have hcol : (L - 1 - (0 - K) : ℕ) = (L - 1 : ℕ) := by omega
  have hrow : (K - 0 : ℕ) = K := by omega
  rw [hcol, hrow]

/-- The last window of the family is the left end window: at `j = L + K - 1` both
offsets collapse to `0`, the start of `verticalStaircaseLeftWindow`. -/
theorem verticalStaircaseWindow_last (s : TorusVertex width height) {L K : ℕ}
    (hL : 0 < L) (hK : 0 < K) :
    verticalStaircaseWindow s L K (L + K - 1) = verticalStaircaseLeftWindow s L K := by
  rw [verticalStaircaseWindow, verticalStaircaseLeftWindow]
  have hcol : (L - 1 - ((L + K - 1) - K) : ℕ) = 0 := by omega
  have hrow : (K - (L + K - 1) : ℕ) = 0 := by omega
  rw [hcol, hrow]
  simp

/-- Every window of the staircase family is an `L × K` cyclic window, hence injective
under the translation-invariant one-orientation window hypotheses.

Source: arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
the section on the window family. -/
theorem NormalTorusArcWindowInjectivityHypotheses.verticalStaircaseWindow_injective
    {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (s : TorusVertex width height) (j : ℕ) :
    κ.IsInjective (verticalStaircaseWindow s L K j) :=
  h.arcWindow_injective _

/-! ### The consecutive-window unions

`verticalStaircaseUnion s L K j` is the union of the two consecutive windows `W_j` and
`W_{j+1}`.  On the descending arm `j < K` the two windows share the column band and
differ by one row, so the union is the `L × (K + 1)` cyclic rectangle of
`verticalAdjacentWindows_union`.  On the right-shifting arm `K ≤ j` the two windows
share the row band and differ by one column, so the union is the `(L + 1) × K` cyclic
rectangle of `horizontalAdjacentWindows_union`. -/

/-- The union of two consecutive windows of the staircase family.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (comparing consecutive windows);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
def verticalStaircaseUnion (s : TorusVertex width height) (L K j : ℕ) :
    Finset (TorusVertex width height) :=
  verticalStaircaseWindow s L K j ∪ verticalStaircaseWindow s L K (j + 1)

/-- **A descending-arm consecutive union is an `L × (K + 1)` cyclic rectangle.**

For `j < K` the windows `W_j` and `W_{j+1}` share the column band
`[a + L - 1, a + 2L - 1)` and differ by one row, so their union is the single
`L × (K + 1)` cyclic rectangle with row start offset `K - (j + 1)`.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the vertical-slide union is an
$L\times(K+1)$ rectangle); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem verticalStaircaseUnion_eq_verticalRectangle {L K : ℕ} (hh : 1 < height)
    (s : TorusVertex width height) {j : ℕ} (hj : j < K) :
    verticalStaircaseUnion s L K j =
      torusArcRectangle
        (s.1 + ((L - 1 : ℕ) : ZMod width), s.2 + ((K - (j + 1) : ℕ) : ZMod height))
        L (K + 1) := by
  rw [verticalStaircaseUnion, verticalStaircaseWindow, verticalStaircaseWindow,
    Finset.union_comm]
  -- The column offsets agree on the descending arm and the row offsets differ by one.
  have hcolj : (L - 1 - (j - K) : ℕ) = (L - 1 : ℕ) := by omega
  have hcolj1 : (L - 1 - ((j + 1) - K) : ℕ) = (L - 1 : ℕ) := by omega
  have hrow : ((K - j : ℕ) : ZMod height) = ((K - (j + 1) : ℕ) : ZMod height) + 1 := by
    rw [show (K - j : ℕ) = (K - (j + 1)) + 1 by omega]; push_cast; ring
  rw [hcolj, hcolj1, hrow, ← add_assoc]
  exact verticalAdjacentWindows_union (by omega) hh
    (s.1 + ((L - 1 : ℕ) : ZMod width), s.2 + ((K - (j + 1) : ℕ) : ZMod height))

/-- **A right-shifting-arm consecutive union is an `(L + 1) × K` cyclic rectangle.**

For `K ≤ j` the windows `W_j` and `W_{j+1}` share the row band `[b, b + K)` and differ
by one column, so their union is the single `(L + 1) × K` cyclic rectangle with column
start offset `(L - 1) - ((j + 1) - K)`.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the consecutive-window union is an
$(L+1)\times K$ rectangle); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem verticalStaircaseUnion_eq_horizontalRectangle {L K : ℕ} (hw : 1 < width)
    (s : TorusVertex width height) {j : ℕ} (hj : K ≤ j) (hjK : j + 1 < L + K) :
    verticalStaircaseUnion s L K j =
      torusArcRectangle
        (s.1 + ((L - 1 - ((j + 1) - K) : ℕ) : ZMod width), s.2) (L + 1) K := by
  rw [verticalStaircaseUnion, verticalStaircaseWindow, verticalStaircaseWindow,
    Finset.union_comm]
  -- The row offsets vanish on the right-shifting arm and the column offsets differ by one.
  have hrowj : (K - j : ℕ) = 0 := by omega
  have hrowj1 : (K - (j + 1) : ℕ) = 0 := by omega
  have hcol : ((L - 1 - (j - K) : ℕ) : ZMod width) =
      ((L - 1 - ((j + 1) - K) : ℕ) : ZMod width) + 1 := by
    rw [show (L - 1 - (j - K) : ℕ) = (L - 1 - ((j + 1) - K)) + 1 by omega]; push_cast; ring
  rw [hrowj, hrowj1, hcol, Nat.cast_zero, add_zero, ← add_assoc]
  exact horizontalAdjacentWindows_union (by omega) hw
    (s.1 + ((L - 1 - ((j + 1) - K) : ℕ) : ZMod width), s.2)

/-- Each consecutive union of the staircase family is injective: on the descending arm
it is the `L × (K + 1)` cyclic rectangle, on the right-shifting arm the `(L + 1) × K`
cyclic rectangle, both injective under the translation-invariant window hypotheses.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem NormalTorusArcWindowInjectivityHypotheses.verticalStaircaseUnion_injective
    {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) (s : TorusVertex width height)
    {j : ℕ} (hjK : j + 1 < L + K) :
    κ.IsInjective (verticalStaircaseUnion s L K j) := by
  by_cases harm : j < K
  · rw [verticalStaircaseUnion_eq_verticalRectangle (by omega) s harm]
    exact h.verticalUnion_injective hUnion hL hK hxw hyh _
  · rw [verticalStaircaseUnion_eq_horizontalRectangle (by omega) s (by omega) hjK]
    exact h.horizontalUnion_injective hUnion hL hK hxw hyh _

/-! ### Membership in the family

The cyclic distances of a window vertex from the staircase corner `s`, read back through
`zmod_val_sub_shift`.  These reduce the subset facts below to natural-number
arithmetic. -/

/-- Membership in `verticalStaircaseWindow s L K j`, in terms of the cyclic distances
from the staircase corner `s`.  On the descending arm `j ≤ K` the column distance lands
in `[L - 1, 2L - 1)` and the row distance in `[K - j, 2K - j)`; on the right-shifting arm
`K ≤ j` the row distance lands in `[0, K)` and the column distance in
`[L - 1 - (j - K), 2L - 1 - (j - K))`.

Source: arXiv:1804.04964, the corollary and proof sketch at lines 2297--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
the section on the window family. -/
theorem mem_verticalStaircaseWindow {L K j : ℕ} (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (s : TorusVertex width height) (v : TorusVertex width height) :
    v ∈ verticalStaircaseWindow s L K j ↔
      ((L - 1 - (j - K) : ℕ) ≤ (v.1 - s.1).val ∧
          (v.1 - s.1).val < (L - 1 - (j - K)) + L) ∧
        ((K - j : ℕ) ≤ (v.2 - s.2).val ∧ (v.2 - s.2).val < (K - j) + K) := by
  have hw0 : 0 < width := NeZero.pos width
  have hh0 : 0 < height := NeZero.pos height
  have hLj : L - 1 - (j - K) ≤ L - 1 := Nat.sub_le _ _
  have hKj : K - j ≤ K := Nat.sub_le _ _
  rw [verticalStaircaseWindow, mem_torusArcRectangle,
    zmod_val_sub_shift width v.1 s.1 (L - 1 - (j - K)) (by omega),
    zmod_val_sub_shift height v.2 s.2 (K - j) (by omega)]
  have hdx := ZMod.val_lt (v.1 - s.1)
  have hdy := ZMod.val_lt (v.2 - s.2)
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> (split_ifs at hx hy with hcx hcy <;> omega)
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    refine ⟨?_, ?_⟩
    · rw [if_neg (by omega)]; omega
    · rw [if_neg (by omega)]; omega

/-! ### The subset nesting `W_j ⊆ U_j ⊆ P`

The nesting consumed by the patch chaining.  Each window sits in its consecutive union
(definitionally), and every window — hence every union — sits in the staircase patch
`P`. -/

/-- The first window of a consecutive union sits in the union (definitionally). -/
theorem verticalStaircaseWindow_subset_verticalStaircaseUnion
    (s : TorusVertex width height) (L K j : ℕ) :
    verticalStaircaseWindow s L K j ⊆ verticalStaircaseUnion s L K j :=
  Finset.subset_union_left

/-- The second window of a consecutive union sits in the union (definitionally). -/
theorem verticalStaircaseWindow_succ_subset_verticalStaircaseUnion
    (s : TorusVertex width height) (L K j : ℕ) :
    verticalStaircaseWindow s L K (j + 1) ⊆ verticalStaircaseUnion s L K j :=
  Finset.subset_union_right

/-- **Each window sits in the staircase patch.**  A descending-arm window `W_j`
(`j ≤ K`) sits in the vertical band `[a + L - 1, a + 2L - 1) × [b, b + 2K)` and a
right-shifting-arm window `W_j` (`K ≤ j`) sits in the horizontal band
`[a, a + 2L - 1) × [b, b + K)`; both bands are part of `P`.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the patch `P = ⋃_j W_j`);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 2. -/
theorem verticalStaircaseWindow_subset_patch {L K j : ℕ} (hL : 0 < L)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    verticalStaircaseWindow s L K j ⊆ verticalStaircasePatch s L K := by
  intro v hv
  rw [mem_verticalStaircaseWindow hxw hyh] at hv
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hv
  rw [verticalStaircasePatch, Finset.mem_union, mem_torusArcRectangle, mem_torusArcRectangle]
  dsimp only
  have hdx := ZMod.val_lt (v.1 - s.1)
  have hdy := ZMod.val_lt (v.2 - s.2)
  have hw0 : 0 < width := NeZero.pos width
  have hLj : L - 1 - (j - K) ≤ L - 1 := Nat.sub_le _ _
  have hKj : K - j ≤ K := Nat.sub_le _ _
  by_cases harm : K ≤ j
  · -- Right-shifting arm: the horizontal band, with row offset `0`.
    right
    exact ⟨by omega, by omega⟩
  · -- Descending arm: the vertical band, column offset `L - 1`.
    left
    rw [zmod_val_sub_shift width v.1 s.1 (L - 1) (by omega)]
    rw [if_neg (by omega)]
    exact ⟨by omega, by omega⟩

/-- **Each consecutive union sits in the staircase patch.**  The union of two windows of
the family, both of which sit in the patch.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 2. -/
theorem verticalStaircaseUnion_subset_patch {L K j : ℕ} (hL : 0 < L)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    verticalStaircaseUnion s L K j ⊆ verticalStaircasePatch s L K := by
  rw [verticalStaircaseUnion, Finset.union_subset_iff]
  exact ⟨verticalStaircaseWindow_subset_patch hL hxw hyh s,
    verticalStaircaseWindow_subset_patch hL hxw hyh s⟩

/-! ### The patch is the union of the family

The staircase patch `P = ⋃_j W_j` is exactly the union of the `L + K` windows of the
family.  The forward inclusion is the per-window subset; the reverse threads a patch
vertex through the arm it lies on — a vertical-band vertex through a descending window, a
horizontal-band vertex through a right-shifting window. -/

/-- **The patch is the union of the staircase family.**  The staircase patch `P` equals
the union of the `L + K` windows `W_0, …, W_{L+K-1}`: every window sits in `P`, and
conversely every vertex of `P` lies in some window — a vertical-band vertex in a
descending window `W_j` with `j ≤ K`, a horizontal-band vertex in a right-shifting window
`W_{K+i}`.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the patch `P = ⋃_j W_j`);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section on the window family. -/
theorem biUnion_verticalStaircaseWindow_eq_patch {L K : ℕ} (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    (Finset.range (L + K)).biUnion (verticalStaircaseWindow s L K) =
      verticalStaircasePatch s L K := by
  apply Finset.Subset.antisymm
  · -- Forward: every window sits in the patch.
    rw [Finset.biUnion_subset]
    exact fun j _ => verticalStaircaseWindow_subset_patch hL hxw hyh s
  · -- Reverse: thread a patch vertex through its arm.
    intro v hv
    simp only [Finset.mem_biUnion, Finset.mem_range]
    rw [verticalStaircasePatch, Finset.mem_union, mem_torusArcRectangle,
      mem_torusArcRectangle] at hv
    dsimp only at hv
    have hw0 : 0 < width := NeZero.pos width
    have hh0 : 0 < height := NeZero.pos height
    have hdx := ZMod.val_lt (v.1 - s.1)
    have hdy := ZMod.val_lt (v.2 - s.2)
    rcases hv with ⟨hcx, hcy⟩ | ⟨hcx, hcy⟩
    · -- Vertical band: a descending window `W_j`, `j = K - min (v.2 - s.2).val K`.
      rw [zmod_val_sub_shift width v.1 s.1 (L - 1) (by omega)] at hcx
      have hnw : ¬ (v.1 - s.1).val < L - 1 := by
        intro h; rw [if_pos h] at hcx; omega
      rw [if_neg hnw] at hcx
      refine ⟨K - min (v.2 - s.2).val K, by omega, ?_⟩
      rw [mem_verticalStaircaseWindow hxw hyh]
      have hcol : L - 1 - ((K - min (v.2 - s.2).val K) - K) = L - 1 := by omega
      have hrow : K - (K - min (v.2 - s.2).val K) = min (v.2 - s.2).val K := by omega
      rw [hcol, hrow]
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    · -- Horizontal band: a right-shifting window `W_{K+i}`,
      -- `i = (L - 1) - min (v.1 - s.1).val (L - 1)`.
      refine ⟨K + ((L - 1) - min (v.1 - s.1).val (L - 1)), by omega, ?_⟩
      rw [mem_verticalStaircaseWindow hxw hyh]
      have hcol : L - 1 - ((K + ((L - 1) - min (v.1 - s.1).val (L - 1))) - K) =
          min (v.1 - s.1).val (L - 1) := by omega
      have hrow : K - (K + ((L - 1) - min (v.1 - s.1).val (L - 1))) = 0 := by omega
      rw [hcol, hrow]
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

end PEPS
end TNLean
