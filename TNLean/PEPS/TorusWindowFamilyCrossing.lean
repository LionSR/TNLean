import TNLean.PEPS.TorusWindowExtraction
import TNLean.PEPS.TorusWindowFamily

/-!
# The reference edge across the staircase window family

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) realizes a virtual operation on the distinguished bond `e`
as a physical operation on any staircase window containing an endpoint of `e`.  The bond-inserted
family the single-bond peeling `regionInsertedCoeff_endWindows_eq_of_staircase` consumes carries an
insert on every staircase window: a bond-inserted insert on the windows where `e` is a boundary
edge, and an interior-bond deformation on the windows where `e` is an interior bond.  Which
construction applies to each window `W_j` is the geometric datum this file supplies.

## The classification

The reference edge `e = horizontalStaircaseReferenceEdge s L K` has endpoints
`e.1.1 = (a + L - 1, b + K - 1)` (the left endpoint `u`) and `e.1.2 = (a + L, b + K - 1)` (the
right endpoint `w`), read off `torusRightEdge_endpoints_of_lt`.  Against the membership
characterization `mem_staircaseWindow`, in the staircase coordinates `s = (a, b)`:

* the right endpoint `w` lies in `W_j` exactly for `j < L` (the sliding arm strictly before the
  corner);
* the left endpoint `u` lies in `W_j` exactly for `1 ≤ j` (every window but the first).

Hence:

* `W_0` (`j = 0`) contains only `w`, so `e` is a boundary edge;
* `W_1, …, W_{L-1}` (`1 ≤ j < L`) contain both endpoints, so `e` is an interior bond;
* `W_L, …, W_{L+K-1}` (`L ≤ j < L + K`) contain only `u`, so `e` is a boundary edge.

This is the per-window split described in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1
(residual piece 1) and the proof sketch's "a virtual operation on a given bond is a physical
operation on any window containing an endpoint": the boundary-edge windows carry the bond-inserted
insert, the interior-bond windows the interior-bond deformation of the genuine block.

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

/-! ### Membership of the two endpoints of the reference edge

The reference edge `e` of the horizontal staircase end pair is the right edge at
`(a + L - 1, b + K - 1)`.  Its two endpoints are the left endpoint `u = e.1.1` and the right
endpoint `w = e.1.2`; the two lemmas below read off, against `mem_staircaseWindow`, exactly which
windows of the family contain each. -/

/-- **The left endpoint of the reference edge lies in `W_j` exactly for `1 ≤ j`.**

The left endpoint `u = e.1.1 = (a + L - 1, b + K - 1)` of the reference edge has column distance
`L - 1` and row distance `K - 1` from the staircase corner `s = (a, b)`.  Against the window
membership characterization `mem_staircaseWindow`, the column distance `L - 1` lands in the
window's column band exactly when the window has slid past the first one (`1 ≤ j`); the row
distance `K - 1` lands in every window's row band.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem referenceEdge_leftEndpoint_mem_staircaseWindow {L K a b j : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height) (hj : j < L + K) :
    (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K).1.1 ∈
        staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j ↔ 1 ≤ j := by
  have hw0 : 0 < width := NeZero.pos width
  -- The reference edge avoids wraparound, so its ordered endpoints are explicit.
  have hp1lt :
      ((a : ZMod width) + ((L - 1 : ℕ) : ZMod width)).val + 1 < width := by
    rw [show (a : ZMod width) + ((L - 1 : ℕ) : ZMod width) = ((a + (L - 1) : ℕ) : ZMod width) by
        push_cast; ring, ZMod.val_natCast_of_lt (by omega)]
    omega
  have href : horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K =
      torusRightEdge ((a : ZMod width) + ((L - 1 : ℕ) : ZMod width),
        (b : ZMod height) + ((K - 1 : ℕ) : ZMod height)) := rfl
  have hep := torusRightEdge_endpoints_of_lt (width := width) (height := height)
    (p := ((a : ZMod width) + ((L - 1 : ℕ) : ZMod width),
      (b : ZMod height) + ((K - 1 : ℕ) : ZMod height))) hp1lt
  rw [href, hep.1, mem_staircaseWindow (by omega) hyh]
  -- The two coordinate distances of `u` from the staircase corner.
  have hd1 : (((a : ZMod width) + ((L - 1 : ℕ) : ZMod width)) - (a : ZMod width)).val = L - 1 := by
    rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega)]
  have hd2 :
      (((b : ZMod height) + ((K - 1 : ℕ) : ZMod height)) - (b : ZMod height)).val = K - 1 := by
    rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega)]
  dsimp only
  rw [hd1, hd2]
  omega

/-- **The right endpoint of the reference edge lies in `W_j` exactly for `j < L`.**

The right endpoint `w = e.1.2 = (a + L, b + K - 1)` of the reference edge has column distance `L`
and row distance `K - 1` from the staircase corner `s = (a, b)`.  Against the window membership
characterization `mem_staircaseWindow`, the column distance `L` lands in the window's column band
`[L - j, 2L - j)` exactly when the window is strictly before the corner (`j < L`); the row distance
`K - 1` lands in every window's row band.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem referenceEdge_rightEndpoint_mem_staircaseWindow {L K a b j : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height) :
    (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K).1.2 ∈
        staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j ↔ j < L := by
  have hw0 : 0 < width := NeZero.pos width
  have hp1lt :
      ((a : ZMod width) + ((L - 1 : ℕ) : ZMod width)).val + 1 < width := by
    rw [show (a : ZMod width) + ((L - 1 : ℕ) : ZMod width) = ((a + (L - 1) : ℕ) : ZMod width) by
        push_cast; ring, ZMod.val_natCast_of_lt (by omega)]
    omega
  have href : horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K =
      torusRightEdge ((a : ZMod width) + ((L - 1 : ℕ) : ZMod width),
        (b : ZMod height) + ((K - 1 : ℕ) : ZMod height)) := rfl
  have hep := torusRightEdge_endpoints_of_lt (width := width) (height := height)
    (p := ((a : ZMod width) + ((L - 1 : ℕ) : ZMod width),
      (b : ZMod height) + ((K - 1 : ℕ) : ZMod height))) hp1lt
  rw [href, hep.2, mem_staircaseWindow (by omega) hyh]
  -- The two coordinate distances of `w` from the staircase corner.
  have hd1 :
      ((((a : ZMod width) + ((L - 1 : ℕ) : ZMod width)) + 1) - (a : ZMod width)).val = L := by
    rw [show (((a : ZMod width) + ((L - 1 : ℕ) : ZMod width)) + 1) - (a : ZMod width) =
        ((L : ℕ) : ZMod width) by
      rw [show ((L : ℕ) : ZMod width) = (((L - 1) + 1 : ℕ) : ZMod width) by congr 1; omega]
      push_cast; ring]
    rw [ZMod.val_natCast_of_lt (by omega)]
  have hd2 :
      (((b : ZMod height) + ((K - 1 : ℕ) : ZMod height)) - (b : ZMod height)).val = K - 1 := by
    rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega)]
  dsimp only
  rw [hd1, hd2]
  omega

/-! ### The classification of the reference edge per window

The two endpoint memberships split the family into boundary-edge windows (`j = 0` or `L ≤ j`) and
interior-bond windows (`1 ≤ j < L`). -/

/-- **The reference edge is a boundary edge of a single-endpoint window.**

For a window `W_j` of the staircase family with `j = 0` (containing only the right endpoint) or
`L ≤ j` (containing only the left endpoint), the reference edge `e` is a boundary edge of `W_j`:
exactly one endpoint of `e` lies in `W_j`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem isRegionBoundaryEdge_staircaseWindow_referenceEdge {L K a b j : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height) (hj : j < L + K)
    (hjcase : j = 0 ∨ L ≤ j) :
    IsRegionBoundaryEdge (G := torusGraph width height)
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) := by
  have hlow := referenceEdge_leftEndpoint_mem_staircaseWindow (width := width) (height := height)
    (b := b) hL hK ha0 haw hyh hj
  have hup := referenceEdge_rightEndpoint_mem_staircaseWindow (width := width) (height := height)
    (b := b) (j := j) hL hK ha0 haw hyh
  rw [IsRegionBoundaryEdge]
  rcases hjcase with hj0 | hjL
  · -- `j = 0`: only the right endpoint `e.1.2` lies in `W_0`.
    subst hj0
    exact Or.inr ⟨fun h => absurd (hlow.mp h) (by omega), hup.mpr (by omega)⟩
  · -- `L ≤ j`: only the left endpoint `e.1.1` lies in `W_j`.
    exact Or.inl ⟨hlow.mpr (by omega), fun h => absurd (hup.mp h) (by omega)⟩

/-- **Both endpoints of the reference edge lie in an interior-bond window.**

For a window `W_j` of the staircase family with `1 ≤ j < L`, both endpoints of the reference edge
`e` lie in `W_j`: the window has slid past the first one but not reached the corner, so it contains
both the left endpoint (`1 ≤ j`) and the right endpoint (`j < L`).

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem referenceEdge_endpoints_mem_staircaseWindow_of_interior {L K a b j : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height) (h1 : 1 ≤ j) (h2 : j < L) :
    (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K).1.1 ∈
        staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j ∧
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K).1.2 ∈
        staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j :=
  ⟨(referenceEdge_leftEndpoint_mem_staircaseWindow (width := width) (height := height)
      (b := b) hL hK ha0 haw hyh (by omega)).mpr h1,
    (referenceEdge_rightEndpoint_mem_staircaseWindow (width := width) (height := height)
      (b := b) (j := j) hL hK ha0 haw hyh).mpr h2⟩

/-- **The reference edge is not a boundary edge of an interior-bond window.**

For a window `W_j` of the staircase family with `1 ≤ j < L`, the reference edge `e` is *not* a
boundary edge of `W_j`: both endpoints of `e` lie in `W_j`
(`referenceEdge_endpoints_mem_staircaseWindow_of_interior`), so `e` is an interior bond of `W_j`.
This is the window on which the bond-inserted family carries the interior-bond deformation of the
genuine block rather than a boundary-edge insert.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem not_isRegionBoundaryEdge_staircaseWindow_referenceEdge_of_interior {L K a b j : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height) (h1 : 1 ≤ j) (h2 : j < L) :
    ¬ IsRegionBoundaryEdge (G := torusGraph width height)
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) := by
  obtain ⟨hlow, hup⟩ := referenceEdge_endpoints_mem_staircaseWindow_of_interior
    (width := width) (height := height) (b := b) hL hK ha0 haw hyh h1 h2
  rw [IsRegionBoundaryEdge]
  rintro (⟨_, hout⟩ | ⟨hout, _⟩)
  · exact hout hup
  · exact hout hlow

end Torus

end PEPS
end TNLean
