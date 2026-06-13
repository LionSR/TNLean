import TNLean.PEPS.TorusWindowPeel2

/-!
# The single-bond peeling of the staircase end-pair equality

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) extracts the bond operator on the distinguished edge `e` from
the open-boundary end-pair equality `staircasePair_insert_eq_open`.  This file performs the peeling
of that equality onto the single bond `e`: when the staircase window inserts are the bond-inserted
inserts on the two end windows (and arbitrary inserts on the intermediate windows) all sharing one
deformed state, the end-pair equality reads as an equality of the two end windows' region-inserted
coefficients across `e`.

## The peeling

The bridge `regionInsertedCoeff_eq_extendInsert_bondInserted` of `TNLean/PEPS/TorusWindowPeel2.lean`
writes the region-inserted coefficient of an end window, with a matrix inserted on `e`, as the
assembled deformed state of the corner-extended bond-inserted insert on the end pair `S`.  The
end-pair equality `staircasePair_insert_eq_open` equates the two corner-extended inserts on `S`,
hence their assembled deformed states.  Chaining the two bridge identities through the end-pair
equality leaves the two end windows' region-inserted coefficients equal across `e`, read off any
global physical configuration.  This is the single-tensor content of the peeling; the cross-tensor
gauge is the algebra-isomorphism step that consumes this equality, the residual recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary and proof sketch at lines
  2296--2445 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ} {L K : ℕ} {B : Tensor (torusGraph width height) d}

/-! ### The reference edge as a boundary edge of the first and last staircase windows

The reference edge `e` is a boundary edge of the right end window `W_0` and the left end window
`W_{L+K-1}`, hence of the first and last staircase windows `staircaseWindow s L K 0` and
`staircaseWindow s L K (L+K-1)`, which are those two windows. -/

/-- The reference edge is a boundary edge of the first staircase window `W_0` (the right end
window).

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem isRegionBoundaryEdge_staircaseWindow_zero_referenceEdge
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height)
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0)
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) := by
  rw [staircaseWindow_zero]
  exact isRegionBoundaryEdge_horizontalStaircaseRightWindow_referenceEdge A hL hK ha0 haw hbh

/-- The reference edge is a boundary edge of the last staircase window `W_{L+K-1}` (the left end
window).

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem isRegionBoundaryEdge_staircaseWindow_last_referenceEdge
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height)
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) := by
  rw [staircaseWindow_last _ hL hK]
  exact isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw hbh

/-! ### The single-bond peeling

The bond-inserted inserts on the two end windows, plugged into the end-pair equality, peel the
equality onto the single bond `e`. -/

/-- **The single-bond peeling of the staircase end-pair equality.**

Given a family of inserts `C` on the staircase windows whose deformed states all equal one common
state, with the first window's insert `C 0` the bond-inserted insert of a matrix `M` on the
reference edge `e` and the last window's insert `C (L+K-1)` the bond-inserted insert of `M'`, the
two end windows' region-inserted coefficients with `M` and `M'` inserted on `e` agree, read off any
global physical configuration `cfg`.

The bridge `regionInsertedCoeff_eq_extendInsert_bondInserted` writes each side as the assembled
deformed state of the corner-extended bond-inserted insert on the end pair `S`; the end-pair
equality `staircasePair_insert_eq_open` equates those two assembled states.  This is the
single-tensor content of the peeling: the cross-tensor gauge `Z` and the conjugation identity are
the algebra-isomorphism step that consumes this equality, the residual recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem regionInsertedCoeff_endWindows_eq_of_staircase {a b : ℕ}
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (M M' : Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
      ℂ)
    (C : ∀ j, RegionInsert (G := torusGraph width height) (d := d)
      B (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j))
    (common : (TorusVertex width height → Fin d) → ℂ)
    (hagree : ∀ j, j < L + K →
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j) (C j) = common)
    (hC0 : C 0 = bondInsertedRegionInsert (G := torusGraph width height) B
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0)
      ⟨_, isRegionBoundaryEdge_staircaseWindow_zero_referenceEdge B
        (by omega) (by omega) ha0 haw hbh⟩ M)
    (hClast : C (L + K - 1) = bondInsertedRegionInsert (G := torusGraph width height) B
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
      ⟨_, isRegionBoundaryEdge_staircaseWindow_last_referenceEdge B
        (by omega) (by omega) ha0 haw hbh⟩ M')
    (cfg : TorusVertex width height → Fin d) :
    regionInsertedCoeff (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0)
        ⟨_, isRegionBoundaryEdge_staircaseWindow_zero_referenceEdge B
          (by omega) (by omega) ha0 haw hbh⟩ M
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg) =
      regionInsertedCoeff (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
        ⟨_, isRegionBoundaryEdge_staircaseWindow_last_referenceEdge B
          (by omega) (by omega) ha0 haw hbh⟩ M'
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg) := by
  -- Bridge each side to the assembled deformed state of the corner-extended bond-inserted insert.
  rw [regionInsertedCoeff_eq_extendInsert_bondInserted
      (staircaseWindow_zero_subset_endPair _ L K) hpos, ← hC0,
    regionInsertedCoeff_eq_extendInsert_bondInserted
      (staircaseWindow_last_subset_endPair (by omega) (by omega) _) hpos, ← hClast]
  -- The end-pair equality equates the two corner-extended inserts on `S`; equal inserts give equal
  -- assembled deformed states.
  rw [staircasePair_insert_eq_open h hUB hpos hL hK hxw hyh _ C common hagree]

end Torus

end PEPS
end TNLean
