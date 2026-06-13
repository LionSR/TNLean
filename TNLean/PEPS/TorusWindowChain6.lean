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

end Torus

end PEPS
end TNLean
