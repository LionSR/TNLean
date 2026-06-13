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

end PEPS
end TNLean
