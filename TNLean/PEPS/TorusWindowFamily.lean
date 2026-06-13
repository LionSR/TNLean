import TNLean.PEPS.TorusWindowChain

/-!
# The staircase window family around a horizontal edge

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) compares, around a horizontal edge, a
family of `L + K` overlapping windows that turn the corner of the edge: the first
`L + 1` slide left across the edge one column at a time, then the last `K - 1`
descend one row at a time.  `TNLean/PEPS/TorusWindowChain.lean` records the two
end windows of this family and the staircase patch they sweep; this file builds
the full indexed family `W_0, …, W_{L+K-1}` interpolating between the end
windows, the consecutive-window unions `U_j = W_j ∪ W_{j+1}`, and the subset
nesting `W_j ⊆ U_j ⊆ P` the patch chaining consumes.  It is scoped in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section on the window family
around an edge.

## The family in staircase coordinates

In the staircase coordinates `s = (a, b)` of the end pair (the edge has endpoints
`(a + L - 1, b + K - 1)` and `(a + L, b + K - 1)`) the windows are the cyclic
`L × K` rectangles

* `W_j = [a + L - j, a + 2L - j) × [b + K - 1, b + 2K - 1)` for `j = 0, …, L`,
  the left-sliding arm sharing the row band `[b + K - 1, b + 2K - 1)`;
* `W_{L + i} = [a, a + L) × [b + K - 1 - i, b + 2K - 1 - i)` for `i = 1, …, K - 1`,
  the descending arm sharing the column band `[a, a + L)`.

The corner window `W_L = [a, a + L) × [b + K - 1, b + 2K - 1)` is the meeting
point of the two arms.  The first window `W_0` is the right end window
`horizontalStaircaseRightWindow` and the last `W_{L+K-1}` is the left end window
`horizontalStaircaseLeftWindow`.  The offsets are read with truncated
subtraction: the column offset `L - j` collapses to `0` on the descending arm and
the row offset `(K - 1) - (j - L)` collapses to `K - 1` on the sliding arm, so a
single formula covers both arms with the corner window `W_L` shared.

## The consecutive-window unions

Two consecutive sliding windows (`j < L`) differ by one column, so their union is
the `(L + 1) × K` cyclic rectangle of `horizontalAdjacentWindows_union`.  Two
consecutive descending windows (`L ≤ j`) differ by one row, so their union is the
`L × (K + 1)` cyclic rectangle of `verticalAdjacentWindows_union`.  The transition
between the two arms is not a separate shape: the corner window `W_L` shares the
column band `[a, a + L)` with its successor `W_{L+1}`, so the union `U_L` is an
ordinary vertical `L × (K + 1)` rectangle and the union `U_{L-1}` an ordinary
horizontal `(L + 1) × K` rectangle.

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

/-! ### The staircase window family -/

/-- The `j`-th window of the horizontal staircase family around an edge, in the
staircase coordinates `s = (a, b)` of the end pair.  It is the cyclic `L × K`
rectangle with column start offset `L - j` (truncated, so `0` on the descending
arm `L ≤ j`) and row start offset `(K - 1) - (j - L)` (truncated, so `K - 1` on
the sliding arm `j ≤ L`):

* `W_j = [a + L - j, a + 2L - j) × [b + K - 1, b + 2K - 1)` for `j ≤ L`;
* `W_{L+i} = [a, a + L) × [b + K - 1 - i, b + 2K - 1 - i)` for `j = L + i`.

The shared corner window `W_L = [a, a + L) × [b + K - 1, b + 2K - 1)` sits at the
meeting of the two arms.

Source: arXiv:1804.04964, the corollary and proof sketch at lines 2297--2445 of
`Papers/1804.04964/paper_normal.tex` (the window family around the edge);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section on the window
family. -/
def staircaseWindow (s : TorusVertex width height) (L K j : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle
    (s.1 + ((L - j : ℕ) : ZMod width), s.2 + ((K - 1 - (j - L) : ℕ) : ZMod height)) L K

/-- The first window of the family is the right end window: at `j = 0` the column
offset is `L` and the row offset `K - 1`, the start of
`horizontalStaircaseRightWindow`. -/
theorem staircaseWindow_zero (s : TorusVertex width height) (L K : ℕ) :
    staircaseWindow s L K 0 = horizontalStaircaseRightWindow s L K := by
  rw [staircaseWindow, horizontalStaircaseRightWindow]
  simp

/-- The last window of the family is the left end window: at `j = L + K - 1` both
offsets collapse to `0`, the start of `horizontalStaircaseLeftWindow`. -/
theorem staircaseWindow_last (s : TorusVertex width height) {L K : ℕ}
    (hL : 0 < L) (hK : 0 < K) :
    staircaseWindow s L K (L + K - 1) = horizontalStaircaseLeftWindow s L K := by
  rw [staircaseWindow, horizontalStaircaseLeftWindow]
  have hcol : (L - (L + K - 1) : ℕ) = 0 := by omega
  have hrow : (K - 1 - ((L + K - 1) - L) : ℕ) = 0 := by omega
  rw [hcol, hrow]
  simp

/-- Every window of the staircase family is an `L × K` cyclic window, hence
injective under the translation-invariant one-orientation window hypotheses.

Source: arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
the section on the window family. -/
theorem NormalTorusArcWindowInjectivityHypotheses.staircaseWindow_injective
    {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (s : TorusVertex width height) (j : ℕ) :
    κ.IsInjective (staircaseWindow s L K j) :=
  h.arcWindow_injective _

/-! ### The consecutive-window unions

`staircaseUnion s L K j` is the union of the two consecutive windows
`W_j` and `W_{j+1}`.  On the sliding arm `j < L` the two windows share the row
band and differ by one column, so the union is the `(L + 1) × K` cyclic rectangle
of `horizontalAdjacentWindows_union`.  On the descending arm `L ≤ j` the two
windows share the column band and differ by one row, so the union is the
`L × (K + 1)` cyclic rectangle of `verticalAdjacentWindows_union`. -/

/-- The union of two consecutive windows of the staircase family.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (comparing consecutive windows);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
def staircaseUnion (s : TorusVertex width height) (L K j : ℕ) :
    Finset (TorusVertex width height) :=
  staircaseWindow s L K j ∪ staircaseWindow s L K (j + 1)

/-- **A sliding-arm consecutive union is an `(L + 1) × K` cyclic rectangle.**

For `j < L` the windows `W_j` and `W_{j+1}` share the row band
`[b + K - 1, b + 2K - 1)` and differ by one column, so their union is the single
`(L + 1) × K` cyclic rectangle with column start offset `L - (j + 1)`.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the consecutive-window union is an
$(L+1)\times K$ rectangle); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem staircaseUnion_eq_horizontalRectangle {L K : ℕ} (hw : 1 < width)
    (s : TorusVertex width height) {j : ℕ} (hj : j < L) :
    staircaseUnion s L K j =
      torusArcRectangle
        (s.1 + ((L - (j + 1) : ℕ) : ZMod width), s.2 + ((K - 1 : ℕ) : ZMod height))
        (L + 1) K := by
  rw [staircaseUnion, staircaseWindow, staircaseWindow,
    Finset.union_comm]
  -- The row offsets agree on the sliding arm and the column offsets differ by one.
  have hcol : ((L - j : ℕ) : ZMod width) = ((L - (j + 1) : ℕ) : ZMod width) + 1 := by
    rw [show (L - j : ℕ) = (L - (j + 1)) + 1 by omega]; push_cast; ring
  have hrowj : (K - 1 - (j - L) : ℕ) = (K - 1 : ℕ) := by omega
  have hrowj1 : (K - 1 - ((j + 1) - L) : ℕ) = (K - 1 : ℕ) := by omega
  rw [hcol, hrowj, hrowj1, ← add_assoc]
  exact horizontalAdjacentWindows_union (by omega) hw
    (s.1 + ((L - (j + 1) : ℕ) : ZMod width), s.2 + ((K - 1 : ℕ) : ZMod height))

/-- **A descending-arm consecutive union is an `L × (K + 1)` cyclic rectangle.**

For `L ≤ j` the windows `W_j` and `W_{j+1}` share the column band `[a, a + L)`
and differ by one row, so their union is the single `L × (K + 1)` cyclic
rectangle with row start offset `(K - 1) - ((j + 1) - L)`.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the vertical-slide union is an
$L\times(K+1)$ rectangle); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem staircaseUnion_eq_verticalRectangle {L K : ℕ} (hh : 1 < height)
    (s : TorusVertex width height) {j : ℕ} (hj : L ≤ j) (hjK : j + 1 < L + K) :
    staircaseUnion s L K j =
      torusArcRectangle
        (s.1, s.2 + ((K - 1 - ((j + 1) - L) : ℕ) : ZMod height)) L (K + 1) := by
  rw [staircaseUnion, staircaseWindow, staircaseWindow,
    Finset.union_comm]
  -- The column offsets vanish on the descending arm and the row offsets differ by one.
  have hcolj : (L - j : ℕ) = 0 := by omega
  have hcolj1 : (L - (j + 1) : ℕ) = 0 := by omega
  have hrow : ((K - 1 - (j - L) : ℕ) : ZMod height) =
      ((K - 1 - ((j + 1) - L) : ℕ) : ZMod height) + 1 := by
    rw [show (K - 1 - (j - L) : ℕ) = (K - 1 - ((j + 1) - L)) + 1 by omega]; push_cast; ring
  rw [hcolj, hcolj1, hrow, Nat.cast_zero, add_zero, ← add_assoc]
  exact verticalAdjacentWindows_union (by omega) hh
    (s.1, s.2 + ((K - 1 - ((j + 1) - L) : ℕ) : ZMod height))

namespace NormalTorusArcWindowInjectivityHypotheses

variable {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}

/-- **A sliding-arm consecutive union is injective.** It is the `(L + 1) × K`
cyclic rectangle of `staircaseUnion_eq_horizontalRectangle`.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem staircaseUnion_horizontal_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height) {j : ℕ} (hj : j < L) :
    κ.IsInjective (staircaseUnion s L K j) := by
  rw [staircaseUnion_eq_horizontalRectangle (by omega) s hj]
  exact h.horizontalUnion_injective hUnion hL hK hxw hyh _

/-- **A descending-arm consecutive union is injective.** It is the `L × (K + 1)`
cyclic rectangle of `staircaseUnion_eq_verticalRectangle`.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem staircaseUnion_vertical_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height) {j : ℕ} (hj : L ≤ j) (hjK : j + 1 < L + K) :
    κ.IsInjective (staircaseUnion s L K j) := by
  rw [staircaseUnion_eq_verticalRectangle (by omega) s hj hjK]
  exact h.verticalUnion_injective hUnion hL hK hxw hyh _

end NormalTorusArcWindowInjectivityHypotheses

/-! ### Membership in the family

The cyclic distances of a window vertex from the staircase corner `s`, read back
through `zmod_val_sub_shift`.  These reduce the subset facts below to natural-number
arithmetic. -/

/-- Membership in `staircaseWindow s L K j`, in terms of the cyclic distances from
the staircase corner `s`.  On the sliding arm `j ≤ L` the column distance lands in
`[L - j, 2L - j)` and the row distance in `[K - 1, 2K - 1)`; on the descending arm
`L ≤ j` the column distance lands in `[0, L)` and the row distance in
`[K - 1 - (j - L), 2K - 1 - (j - L))`.

Source: arXiv:1804.04964, the corollary and proof sketch at lines 2297--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
the section on the window family. -/
theorem mem_staircaseWindow {L K j : ℕ} (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (s : TorusVertex width height) (v : TorusVertex width height) :
    v ∈ staircaseWindow s L K j ↔
      ((L - j : ℕ) ≤ (v.1 - s.1).val ∧ (v.1 - s.1).val < (L - j) + L) ∧
        ((K - 1 - (j - L) : ℕ) ≤ (v.2 - s.2).val ∧
          (v.2 - s.2).val < (K - 1 - (j - L)) + K) := by
  have hw0 : 0 < width := NeZero.pos width
  have hh0 : 0 < height := NeZero.pos height
  have hLj : L - j ≤ L := Nat.sub_le _ _
  have hKj : K - 1 - (j - L) ≤ K - 1 := Nat.sub_le _ _
  rw [staircaseWindow, mem_torusArcRectangle,
    zmod_val_sub_shift width v.1 s.1 (L - j) (by omega),
    zmod_val_sub_shift height v.2 s.2 (K - 1 - (j - L)) (by omega)]
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

The nesting consumed by the patch chaining.  Each window sits in its consecutive
union (definitionally), and every window — hence every union — sits in the
staircase patch `P`. -/

/-- The first window of a consecutive union sits in the union (definitionally). -/
theorem staircaseWindow_subset_staircaseUnion (s : TorusVertex width height) (L K j : ℕ) :
    staircaseWindow s L K j ⊆ staircaseUnion s L K j :=
  Finset.subset_union_left

/-- The second window of a consecutive union sits in the union (definitionally). -/
theorem staircaseWindow_succ_subset_staircaseUnion (s : TorusVertex width height) (L K j : ℕ) :
    staircaseWindow s L K (j + 1) ⊆ staircaseUnion s L K j :=
  Finset.subset_union_right

/-- **Each window sits in the staircase patch.**  A sliding-arm window `W_j`
(`j ≤ L`) sits in the horizontal band `[a, a + 2L) × [b + K - 1, b + 2K - 1)` and
a descending-arm window `W_j` (`L ≤ j`) sits in the vertical band
`[a, a + L) × [b, b + 2K - 1)`; both bands are part of `P`.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the patch `P = ⋃_j W_j`);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 2. -/
theorem staircaseWindow_subset_patch {L K j : ℕ} (hK : 0 < K)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    staircaseWindow s L K j ⊆ horizontalStaircasePatch s L K := by
  intro v hv
  rw [mem_staircaseWindow hxw hyh] at hv
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hv
  rw [horizontalStaircasePatch, Finset.mem_union, mem_torusArcRectangle, mem_torusArcRectangle]
  dsimp only
  have hdx := ZMod.val_lt (v.1 - s.1)
  have hdy := ZMod.val_lt (v.2 - s.2)
  have hh0 : 0 < height := NeZero.pos height
  have hLj : L - j ≤ L := Nat.sub_le _ _
  have hKj : K - 1 - (j - L) ≤ K - 1 := Nat.sub_le _ _
  by_cases harm : j ≤ L
  · -- Sliding arm: the horizontal band, with row offset `K - 1`.
    left
    rw [show ((K - 1 : ℕ) : ZMod height) = ((K - 1 : ℕ) : ZMod height) from rfl,
      zmod_val_sub_shift height v.2 s.2 (K - 1) (by omega)]
    rw [if_neg (by omega)]
    refine ⟨by omega, by omega⟩
  · -- Descending arm: the vertical band, column offset `0`.
    right
    refine ⟨by omega, by omega⟩

/-- **Each consecutive union sits in the staircase patch.**  The union of two
windows of the family, both of which sit in the patch.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 2. -/
theorem staircaseUnion_subset_patch {L K j : ℕ} (hK : 0 < K)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    staircaseUnion s L K j ⊆ horizontalStaircasePatch s L K := by
  rw [staircaseUnion, Finset.union_subset_iff]
  exact ⟨staircaseWindow_subset_patch hK hxw hyh s, staircaseWindow_subset_patch hK hxw hyh s⟩

end PEPS
end TNLean
