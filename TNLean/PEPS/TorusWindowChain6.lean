import TNLean.PEPS.TorusWindowChain5
import TNLean.PEPS.TorusWindowFamily

/-!
# The open-boundary staircase chaining and the end-pair equality

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) finishes Steps 2 and 3 of its proof sketch at the
*open-boundary* level: the consecutive-window open-boundary equalities of Step 1 chain across
the staircase patch `P` into one comparison of the two end windows (Step 2), and the shared
injective completed corner cancels to leave the equality on the staircase end pair `S` (Step 3).
This file assembles those two steps from the landed engines, producing the hcompl-free
end-pair equality `staircasePair_insert_eq_open`, never inverting the non-injective torus
complement `univ \ S` (the obstruction recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3).

## The consecutive-window comparison on the staircase union

Each consecutive union `U_j = W_j ∪ W_{j+1}` of the staircase family is a cyclic rectangle:
the `(L + 1) × K` horizontal slide for `j < L` (`staircaseUnion_eq_horizontalRectangle`) or the
`L × (K + 1)` vertical slide for `L ≤ j` (`staircaseUnion_eq_verticalRectangle`), with injective
torus complement at the minimal sizes.  Reading each single-window deformed state as the union
deformed state of its corner-extended insert (`deformedRegionState_extend`) and inverting the
union complement gives the open-boundary equality of the corner-extended inserts on `U_j`,
`extendInsert (W_j ⊆ U_j) (C j) = extendInsert (W_{j+1} ⊆ U_j) (C (j+1))`.  The vertical version
`verticalConsecutiveWindow_extend_eq` mirrors the horizontal `horizontalConsecutiveWindow_extend_eq`
of `TNLean/PEPS/TorusWindowChain2.lean` with the axes transposed.

## The chaining and the cancellation

Extending each consecutive-window equality through `extendInsert (U_j ⊆ P)` and collapsing the
composition by the transitivity `extendInsert_trans` of `TNLean/PEPS/TorusWindowChain4.lean`
chains the `L + K - 1` equalities into one patch-level equality
`extendInsert (W_0 ⊆ P) (C 0) = extendInsert (W_{L+K-1} ⊆ P) (C (L+K-1))`, the lemma
`staircasePatch_insert_eq`.
One more transitivity step through the completed corner and the shared-corner cancellation
`staircasePair_cancel` of `TNLean/PEPS/TorusWindowChain5.lean` strips the patch equality to the
end-pair equality, needing only injectivity of the completed corner `Q` and never of `univ \ S`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and proof
  sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Steps 2--3.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ} {L K : ℕ} {B : Tensor (torusGraph width height) d}

/-! ### The consecutive-window comparison on the staircase union

The descending-arm comparison `verticalConsecutiveWindow_extend_eq` transposes the
horizontal slide of `horizontalConsecutiveWindow_extend_eq`: the consecutive union is the
`L × (K + 1)` cyclic rectangle, its complement injective by
`regionBlockedTensorInjective_verticalUnionComplement`. -/

/-- **The consecutive-window comparison, descending arm (vertical slide).**

For a descending-arm index `L ≤ j` with `j + 1 < L + K`, the two consecutive windows
`W_j` and `W_{j+1}` have union the `L × (K + 1)` cyclic rectangle
(`staircaseUnion_eq_verticalRectangle`).  If their deformed states agree as functions of the
full physical configuration, then the corner-extended inserts on their union are equal: the
open-boundary equality on `U_j`.  Each window state is the union state of its corner-extended
insert (`deformedRegionState_extend`); the agreement transfers to the union states, and
inverting the union complement (`regionBlockedTensorInjective_verticalUnionComplement`) strips
the equal closed-torus states to the equal inserts.  This is the transpose of
`horizontalConsecutiveWindow_extend_eq`.

Source: arXiv:1804.04964, the one-dimensional inversions at lines 2133--2179 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem verticalConsecutiveWindow_extend_eq
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height) {j : ℕ} (hj : L ≤ j) (hjK : j + 1 < L + K)
    (C₁ : RegionInsert (G := torusGraph width height) (d := d) B (staircaseWindow s L K j))
    (C₂ : RegionInsert (G := torusGraph width height) (d := d) B (staircaseWindow s L K (j + 1)))
    (hstate : deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K j) C₁ =
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K (j + 1)) C₂) :
    extendInsert (G := torusGraph width height)
        (staircaseWindow_subset_staircaseUnion s L K j) C₁ =
      extendInsert (G := torusGraph width height)
        (staircaseWindow_succ_subset_staircaseUnion s L K j) C₂ := by
  -- The union complement is blocked-tensor injective: the union is the `L × (K + 1)` rectangle.
  have hcompl : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ staircaseUnion s L K j) := by
    rw [staircaseUnion_eq_verticalRectangle (by omega) s hj hjK]
    exact h.regionBlockedTensorInjective_verticalUnionComplement hUB hL hK hxw hyh _
  -- Both extended inserts have equal union deformed states.
  refine deformedRegionStateAssembled_insert_eq_of_complementInjective
    (G := torusGraph width height) B (staircaseUnion s L K j) hcompl _ _ ?_
  funext cfg
  rw [← deformedRegionState_extend
      (staircaseWindow_subset_staircaseUnion s L K j) hpos C₁,
    ← deformedRegionState_extend
      (staircaseWindow_succ_subset_staircaseUnion s L K j) hpos C₂,
    hstate]

/-- **The consecutive-window comparison, sliding arm (horizontal slide).**

For a sliding-arm index `j < L`, the two consecutive windows `W_j` and `W_{j+1}` have union
the `(L + 1) × K` cyclic rectangle (`staircaseUnion_eq_horizontalRectangle`).  If their deformed
states agree, then the corner-extended inserts on their union are equal.  This is the
`staircaseWindow`-level form of `horizontalConsecutiveWindow_extend_eq`, inverting the union
complement (`regionBlockedTensorInjective_horizontalUnionComplement`) directly on the union.

Source: arXiv:1804.04964, the one-dimensional inversions at lines 2133--2179 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem horizontalStaircaseConsecutiveWindow_extend_eq
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height) {j : ℕ} (hj : j < L)
    (C₁ : RegionInsert (G := torusGraph width height) (d := d) B (staircaseWindow s L K j))
    (C₂ : RegionInsert (G := torusGraph width height) (d := d) B (staircaseWindow s L K (j + 1)))
    (hstate : deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K j) C₁ =
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K (j + 1)) C₂) :
    extendInsert (G := torusGraph width height)
        (staircaseWindow_subset_staircaseUnion s L K j) C₁ =
      extendInsert (G := torusGraph width height)
        (staircaseWindow_succ_subset_staircaseUnion s L K j) C₂ := by
  -- The union complement is blocked-tensor injective: the union is the `(L + 1) × K` rectangle.
  have hcompl : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ staircaseUnion s L K j) := by
    rw [staircaseUnion_eq_horizontalRectangle (by omega) s hj]
    exact h.regionBlockedTensorInjective_horizontalUnionComplement hUB hL hK hxw hyh _
  refine deformedRegionStateAssembled_insert_eq_of_complementInjective
    (G := torusGraph width height) B (staircaseUnion s L K j) hcompl _ _ ?_
  funext cfg
  rw [← deformedRegionState_extend
      (staircaseWindow_subset_staircaseUnion s L K j) hpos C₁,
    ← deformedRegionState_extend
      (staircaseWindow_succ_subset_staircaseUnion s L K j) hpos C₂,
    hstate]

/-! ### The per-step patch-level equality

Each consecutive-window equality lives on the union `U_j`.  Extending both sides through
`extendInsert (U_j ⊆ P)` and collapsing the composition by the transitivity `extendInsert_trans`
of `TNLean/PEPS/TorusWindowChain4.lean` (`extendInsert (U_j ⊆ P) (extendInsert (W_j ⊆ U_j) C) =
extendInsert (W_j ⊆ P) C`, using the nesting `W_j ⊆ U_j ⊆ P`) raises the equality to the patch
`P`.  The arm split on `j < L` vs `L ≤ j` selects the horizontal or vertical consecutive
comparison; the patch-level form is the same on both arms. -/

/-- **The per-step patch-level equality.** For any `j + 1 < L + K`, if the deformed states of
the consecutive windows `W_j` and `W_{j+1}` agree, then the corner-extended inserts on the patch
`P` agree: `extendInsert (W_j ⊆ P) (C j) = extendInsert (W_{j+1} ⊆ P) (C (j+1))`.  The
appropriate arm's consecutive comparison gives the equality on the union `U_j`; extending both
sides through `extendInsert (U_j ⊆ P)` and collapsing by `extendInsert_trans` raises it to `P`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the chained extensions across the patch);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 2. -/
theorem staircaseStep_patch_extend_eq
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height) {j : ℕ} (hjK : j + 1 < L + K)
    (C₁ : RegionInsert (G := torusGraph width height) (d := d) B (staircaseWindow s L K j))
    (C₂ : RegionInsert (G := torusGraph width height) (d := d) B (staircaseWindow s L K (j + 1)))
    (hstate : deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K j) C₁ =
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K (j + 1)) C₂) :
    extendInsert (G := torusGraph width height)
        (staircaseWindow_subset_patch (j := j) (by omega) (by omega) (by omega) s) C₁ =
      extendInsert (G := torusGraph width height)
        (staircaseWindow_subset_patch (j := j + 1) (by omega) (by omega) (by omega) s) C₂ := by
  -- The union-level open-boundary equality of the two corner-extended inserts.
  have hU : extendInsert (G := torusGraph width height)
        (staircaseWindow_subset_staircaseUnion s L K j) C₁ =
      extendInsert (G := torusGraph width height)
        (staircaseWindow_succ_subset_staircaseUnion s L K j) C₂ := by
    rcases lt_or_ge j L with hj | hj
    · exact horizontalStaircaseConsecutiveWindow_extend_eq h hUB hpos hL hK hxw hyh s hj C₁ C₂
        hstate
    · exact verticalConsecutiveWindow_extend_eq h hUB hpos hL hK hxw hyh s hj hjK C₁ C₂ hstate
  -- Extend both union-level inserts through `extendInsert (U_j ⊆ P)`; collapse by transitivity.
  have hUP : staircaseUnion s L K j ⊆ horizontalStaircasePatch s L K :=
    staircaseUnion_subset_patch (by omega) (by omega) (by omega) s
  have e₁ := extendInsert_trans (G := torusGraph width height)
    (staircaseWindow_subset_staircaseUnion s L K j) hUP hpos C₁
  have e₂ := extendInsert_trans (G := torusGraph width height)
    (staircaseWindow_succ_subset_staircaseUnion s L K j) hUP hpos C₂
  rw [← e₁, ← e₂, hU]

/-! ### The patch chaining

Chaining the per-step patch-level equalities over `j = 0, …, L + K - 2` by transitivity gives
one comparison of the two end windows on the patch.  The chain is a `Nat`-induction over the
window index: at each step the per-step equality `staircaseStep_patch_extend_eq` advances the
patch-extended insert from window `W_j` to `W_{j+1}`, the intermediate windows dropping out since
all single-window deformed states equal one common state. -/

/-- **The patch chaining (Step 2).** Given a family of deformed inserts `C j` on the staircase
windows, all of whose deformed states equal one common state, the patch-extended inserts of the
first window `W_0` and any window `W_n` (`n < L + K`) agree on the patch `P`.  Induction on `n`:
the base case is reflexivity, and the step uses the per-step patch-level equality
`staircaseStep_patch_extend_eq` at index `n`, whose hypothesis follows from the common-state
agreement at `n` and `n + 1`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (chaining the windows across the patch);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 2. -/
theorem staircasePatch_insert_eq_aux
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height)
    (C : ∀ j, RegionInsert (G := torusGraph width height) (d := d) B (staircaseWindow s L K j))
    (common : (TorusVertex width height → Fin d) → ℂ)
    (hagree : ∀ j, j < L + K →
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K j) (C j) = common) :
    ∀ n, n < L + K →
      extendInsert (G := torusGraph width height)
          (staircaseWindow_subset_patch (j := 0) (by omega) (by omega) (by omega) s) (C 0) =
        extendInsert (G := torusGraph width height)
          (staircaseWindow_subset_patch (j := n) (by omega) (by omega) (by omega) s) (C n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    -- The per-step equality advances the patch-extended insert from `W_n` to `W_{n+1}`.
    have hstep := staircaseStep_patch_extend_eq h hUB hpos hL hK hxw hyh s (j := n) hn
      (C n) (C (n + 1)) ((hagree n (by omega)).trans (hagree (n + 1) hn).symm)
    exact (ih (by omega)).trans hstep

/-- **The patch chaining (Step 2), end-pair form.** Given a family of deformed inserts on the
staircase windows all sharing one deformed state, the patch-extended inserts of the two end
windows `W_0` and `W_{L+K-1}` agree on the patch `P`.  This is
`staircasePatch_insert_eq_aux` specialized to `n = L + K - 1`, the index of the last window.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (chaining the windows across the patch);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 2. -/
theorem staircasePatch_insert_eq
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height)
    (C : ∀ j, RegionInsert (G := torusGraph width height) (d := d) B (staircaseWindow s L K j))
    (common : (TorusVertex width height → Fin d) → ℂ)
    (hagree : ∀ j, j < L + K →
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K j) (C j) = common) :
    extendInsert (G := torusGraph width height)
        (staircaseWindow_subset_patch (j := 0) (by omega) (by omega) (by omega) s) (C 0) =
      extendInsert (G := torusGraph width height)
        (staircaseWindow_subset_patch (j := L + K - 1) (by omega) (by omega) (by omega) s)
        (C (L + K - 1)) :=
  staircasePatch_insert_eq_aux h hUB hpos hL hK hxw hyh s C common hagree (L + K - 1) (by omega)

/-! ### The corner-completion nesting

The patch `P = S ∪ corner` sits inside the completed union `S ∪ Q`, where `Q` is the completed
corner (the `L × K` rectangle obtained from the `L × (K - 1)` corner block by adding one row).
These two nestings — the end pair inside the patch, and the patch inside the completed union —
extend the patch chaining to the completed union, where the shared injective `Q` cancels. -/

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- The `L × (K - 1)` corner block sits inside the `L × K` completed corner `Q`: same cyclic
start, the height truncated. -/
theorem horizontalStaircaseCorner_subset_completedCorner (s : TorusVertex width height) :
    horizontalStaircaseCorner s L K ⊆ horizontalStaircaseCompletedCorner s L K := by
  intro v hv
  rw [horizontalStaircaseCorner, mem_torusArcRectangle] at hv
  rw [horizontalStaircaseCompletedCorner, mem_torusArcRectangle]
  exact ⟨hv.1, hv.2.trans_le (Nat.sub_le _ _)⟩

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- The staircase end pair sits inside the patch: `P = S ∪ corner`, so `S ⊆ P`. -/
theorem horizontalStaircaseEndPair_subset_patch {L K : ℕ} (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    horizontalStaircaseEndPair s L K ⊆ horizontalStaircasePatch s L K := by
  rw [horizontalStaircasePatch_eq_endPair_union_corner hL hK hxw hyh s]
  exact Finset.subset_union_left

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- The patch sits inside the completed union: `P = S ∪ corner ⊆ S ∪ Q`, the corner block
`corner ⊆ Q` being completed by one row. -/
theorem horizontalStaircasePatch_subset_completedUnion {L K : ℕ} (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    horizontalStaircasePatch s L K ⊆
      horizontalStaircaseEndPair s L K ∪ horizontalStaircaseCompletedCorner s L K := by
  rw [horizontalStaircasePatch_eq_endPair_union_corner hL hK hxw hyh s]
  exact Finset.union_subset_union_right
    (horizontalStaircaseCorner_subset_completedCorner s)

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- The first window `W_0` sits inside the end pair: at `j = 0` it is the right end window. -/
theorem staircaseWindow_zero_subset_endPair (s : TorusVertex width height) (L K : ℕ) :
    staircaseWindow s L K 0 ⊆ horizontalStaircaseEndPair s L K := by
  rw [staircaseWindow_zero]
  exact horizontalStaircaseRightWindow_subset_endPair s

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- The last window `W_{L+K-1}` sits inside the end pair: it is the left end window. -/
theorem staircaseWindow_last_subset_endPair {L K : ℕ} (hL : 0 < L) (hK : 0 < K)
    (s : TorusVertex width height) :
    staircaseWindow s L K (L + K - 1) ⊆ horizontalStaircaseEndPair s L K := by
  rw [staircaseWindow_last s hL hK]
  exact horizontalStaircaseLeftWindow_subset_endPair s

/-! ### The hcompl-free end-pair equality

Extending the patch chaining `staircasePatch_insert_eq` through the corner-completion nesting and
cancelling the shared injective completed corner `Q` by `staircasePair_cancel` of
`TNLean/PEPS/TorusWindowChain5.lean` strips the patch equality to the open-boundary equality on
the staircase end pair `S = W_0 ⊔ W_{L+K-1}`.  The cancellation needs only injectivity of `Q`
(an `L × K` window, injective by hypothesis) and never of the non-injective torus complement
`univ \ S`: this is the hcompl-free Step 3 the note's corner completion delivers. -/

/-- **The hcompl-free staircase end-pair equality (Steps 2--3).**

Given a family of deformed inserts `C j` on the staircase windows `W_0, …, W_{L+K-1}` around a
horizontal edge, all of whose deformed states equal one common state, the corner-extended inserts
of the two end windows agree on the staircase end pair `S = W_0 ⊔ W_{L+K-1}`:
`extendInsert (W_0 ⊆ S) (C 0) = extendInsert (W_{L+K-1} ⊆ S) (C (L+K-1))`.

The patch chaining `staircasePatch_insert_eq` raises the agreement to the patch
`extendInsert (W_0 ⊆ P) (C 0) = extendInsert (W_{L+K-1} ⊆ P) (C (L+K-1))`; extending both sides
through `extendInsert (P ⊆ S ∪ Q)` and collapsing the chains `W_0 ⊆ S ⊆ S ∪ Q` and
`W_0 ⊆ P ⊆ S ∪ Q` (and the `W_{L+K-1}` analogues) by `extendInsert_trans` presents the two
end-pair inserts with equal extensions through the completed union; the shared-corner cancellation
`staircasePair_cancel` cancels the injective `Q = horizontalStaircaseCompletedCorner` to leave the
equality on `S`.  Only `Q` injectivity is used — derived from the window hypotheses through
`horizontalStaircaseCompletedCorner_injective` — never `univ \ S` injectivity, the obstruction
recorded in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (add two-two tensors in the corner and invert);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Steps 2--3. -/
theorem staircasePair_insert_eq_open
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height)
    (C : ∀ j, RegionInsert (G := torusGraph width height) (d := d) B (staircaseWindow s L K j))
    (common : (TorusVertex width height → Fin d) → ℂ)
    (hagree : ∀ j, j < L + K →
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K j) (C j) = common) :
    extendInsert (G := torusGraph width height)
        (staircaseWindow_zero_subset_endPair s L K) (C 0) =
      extendInsert (G := torusGraph width height)
        (staircaseWindow_last_subset_endPair (by omega) (by omega) s) (C (L + K - 1)) := by
  -- The shared injective completed corner `Q`, as blocked-tensor injectivity.
  have hQ : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseCompletedCorner s L K) := by
    have hi := h.horizontalStaircaseCompletedCorner_injective s
    rwa [regionInjectivityDataOf_isInjective] at hi
  -- The patch chaining: the two end windows' patch-extended inserts agree.
  have hpatch := staircasePatch_insert_eq h hUB hpos hL hK hxw hyh s C common hagree
  -- The corner-completion nestings.
  have hPcU : horizontalStaircasePatch s L K ⊆
      horizontalStaircaseEndPair s L K ∪ horizontalStaircaseCompletedCorner s L K :=
    horizontalStaircasePatch_subset_completedUnion (by omega) (by omega) (by omega) (by omega) s
  have hScU : horizontalStaircaseEndPair s L K ⊆
      horizontalStaircaseEndPair s L K ∪ horizontalStaircaseCompletedCorner s L K :=
    horizontalStaircaseEndPair_subset_completedUnion s
  have hW0P : staircaseWindow s L K 0 ⊆ horizontalStaircasePatch s L K :=
    staircaseWindow_subset_patch (j := 0) (by omega) (by omega) (by omega) s
  have hWendP : staircaseWindow s L K (L + K - 1) ⊆ horizontalStaircasePatch s L K :=
    staircaseWindow_subset_patch (j := L + K - 1) (by omega) (by omega) (by omega) s
  -- Cancel the shared injective completed corner `Q`.
  refine staircasePair_cancel s (by omega) (by omega) hpos hQ _ _ ?_
  -- Both end-pair inserts extend to the same insert on `S ∪ Q`, bridged by the patch equality.
  rw [extendInsert_trans (staircaseWindow_zero_subset_endPair s L K) hScU hpos (C 0),
    extendInsert_trans (staircaseWindow_last_subset_endPair (by omega) (by omega) s) hScU hpos
      (C (L + K - 1)),
    ← extendInsert_trans hW0P hPcU hpos (C 0),
    ← extendInsert_trans hWendP hPcU hpos (C (L + K - 1)), hpatch]

end Torus

end PEPS
end TNLean
