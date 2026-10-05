/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRectangleBoundaryCard
import Mathlib.Data.Fintype.EquivFin

/-!
# Clockwise native boundary of a CZX rectangle

The crossing bonds of a positive proper coordinate rectangle are numbered
clockwise: top from left to right, right from top to bottom, bottom from
right to left, and left from bottom to top. The numbering is by the actual
cyclic index `Fin (2 * xLen + 2 * yLen)`. Its consecutive endpoints are the
plaquette corners carrying the effective CZX boundary qubits.

These are auxiliary lattice-geometry results for the region boundary in
Chen, Liu, and Wen, arXiv:1106.4752, source lines 330–345. The rectangle may
meet a coordinate seam.

**Scope restriction (rectangular region):** both periods are at least three,
and both positive rectangle sides are shorter than their periods. See
`docs/paper-gaps/rmp_peps_czx_boundary_chain.tex`.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752), CZX model boundary, lines 330–345.
-/

namespace TNLean.PEPS

/-- The first plaquette corner of each clockwise perimeter segment, in
coordinates relative to the lower-left corner of the rectangle. -/
def rectanglePerimeterCorner (w h : ℕ) (i : Fin (2 * w + 2 * h)) : ℕ × ℕ :=
  if i.val < w then (i.val, h)
  else if i.val < w + h then (w, w + h - i.val)
  else if i.val < 2 * w + h then (2 * w + h - i.val, 0)
  else (0, i.val - (2 * w + h))

/-- The second plaquette corner of a clockwise perimeter segment. -/
def rectanglePerimeterEnd (w h : ℕ) (i : Fin (2 * w + 2 * h)) : ℕ × ℕ :=
  if i.val < w then (i.val + 1, h)
  else if i.val < w + h then (w, w + h - 1 - i.val)
  else if i.val < 2 * w + h then (2 * w + h - 1 - i.val, 0)
  else (0, i.val - (2 * w + h) + 1)

/-- Bottom and left native bonds carry their two qubits in the reverse of
clockwise perimeter order. -/
def rectanglePerimeterReversed (w h : ℕ) (i : Fin (2 * w + 2 * h)) : Bool :=
  decide (w + h ≤ i.val)

/-- A rectangular perimeter has even length. -/
theorem even_rectanglePerimeter (w h : ℕ) : Even (2 * w + 2 * h) := by
  exact ⟨w + h, by omega⟩

/-- Consecutive clockwise segments share exactly the corner used by the
cyclic boundary-qubit convention. The successor is the usual `Fin` addition. -/
theorem rectanglePerimeterEnd_eq_corner_add_one (w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) [NeZero (2 * w + 2 * h)]
    (i : Fin (2 * w + 2 * h)) :
    rectanglePerimeterEnd w h i = rectanglePerimeterCorner w h (i + 1) := by
  have hn : 1 < 2 * w + 2 * h := by omega
  have hv : (i + 1).val = (i.val + 1) % (2 * w + 2 * h) := by
    rw [Fin.val_add]
    change (i.val + 1 % (2 * w + 2 * h)) % (2 * w + 2 * h) = _
    rw [Nat.mod_eq_of_lt hn]
  by_cases hi : i.val + 1 < 2 * w + 2 * h
  · rw [Nat.mod_eq_of_lt hi] at hv
    unfold rectanglePerimeterEnd rectanglePerimeterCorner
    rw [hv]
    split_ifs <;> apply Prod.ext <;> dsimp only <;> omega
  · have hv0 : (i + 1).val = 0 := by
      rw [hv, show i.val + 1 = 2 * w + 2 * h by omega, Nat.mod_self]
    unfold rectanglePerimeterEnd rectanglePerimeterCorner
    rw [hv0]
    split_ifs <;> apply Prod.ext <;> dsimp only <;> omega

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Native horizontal or vertical bond coordinates in clockwise rectangle
order. Bottom and left bonds use the preceding row or column, including
wraparound when the rectangle starts at zero. -/
def torusRectanglePerimeterCode (xStart yStart w h : ℕ)
    (i : Fin (2 * w + 2 * h)) :
    TorusVertex width height ⊕ TorusVertex width height :=
  if i.val < w then
    Sum.inr (((xStart + i.val : ℕ) : ZMod width), ((yStart + h - 1 : ℕ) : ZMod height))
  else if i.val < w + h then
    Sum.inl (((xStart + w - 1 : ℕ) : ZMod width),
      ((yStart + (w + h - 1 - i.val) : ℕ) : ZMod height))
  else if i.val < 2 * w + h then
    Sum.inr (((xStart + (2 * w + h - 1 - i.val) : ℕ) : ZMod width),
      (yStart : ZMod height) - 1)
  else
    Sum.inl ((xStart : ZMod width) - 1,
      ((yStart + (i.val - (2 * w + h)) : ℕ) : ZMod height))

/-- The actual torus crossing bond at a clockwise perimeter index. -/
noncomputable def torusRectanglePerimeterEdge (xStart yStart w h : ℕ)
    (i : Fin (2 * w + 2 * h)) : Edge (torusGraph width height) :=
  torusEdgeEquiv (torusRectanglePerimeterCode xStart yStart w h i)

private theorem rectangle_interval_end_out {n : ℕ} [NeZero n]
    (s l : ℕ) (_hl : 0 < l) (hb : s + l ≤ n) (hp : l < n) :
    ¬(s ≤ ((s + l : ℕ) : ZMod n).val ∧ ((s + l : ℕ) : ZMod n).val < s + l) := by
  by_cases hlt : s + l < n
  · rw [ZMod.val_natCast_of_lt hlt]
    omega
  · have he : s + l = n := by omega
    rw [he, ZMod.natCast_self, ZMod.val_zero]
    omega

private theorem rectangle_interval_pred_out {n : ℕ} [NeZero n] [Fact (1 < n)]
    (s l : ℕ) (hl : 0 < l) (hb : s + l ≤ n) (hp : l < n) :
    ¬(s ≤ ((s : ZMod n) - 1).val ∧ ((s : ZMod n) - 1).val < s + l) := by
  intro hm
  have hs : s < n := by omega
  have he := congrArg ZMod.val (sub_add_cancel (s : ZMod n) 1)
  rw [ZMod.val_add, ZMod.val_one, ZMod.val_natCast_of_lt hs] at he
  by_cases hv : ((s : ZMod n) - 1).val + 1 < n
  · rw [Nat.mod_eq_of_lt hv] at he
    omega
  · have hv' : ((s : ZMod n) - 1).val + 1 = n := by
      have := ZMod.val_lt ((s : ZMod n) - 1)
      omega
    rw [hv', Nat.mod_self] at he
    omega

private theorem rectangle_interval_last_ne_pred {n : ℕ} [NeZero n] [Fact (1 < n)]
    (s l : ℕ) (hl : 0 < l) (hb : s + l ≤ n) (hp : l < n) :
    ((s + l - 1 : ℕ) : ZMod n) ≠ (s : ZMod n) - 1 := by
  intro he
  have hm : s ≤ ((s + l - 1 : ℕ) : ZMod n).val ∧
      ((s + l - 1 : ℕ) : ZMod n).val < s + l := by
    rw [ZMod.val_natCast_of_lt (show s + l - 1 < n by omega)]
    omega
  rw [he] at hm
  exact rectangle_interval_pred_out s l hl hb hp hm

private theorem rectangle_boundary_up (xStart yStart w h : ℕ)
    (_hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hp : h < height) (k : ℕ) (hk : k < w) :
    IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart w h)
      (torusUpEdge (((xStart + k : ℕ) : ZMod width),
        ((yStart + h - 1 : ℕ) : ZMod height))) := by
  have hstep : (((yStart + h - 1 : ℕ) : ZMod height) + 1) =
      ((yStart + h : ℕ) : ZMod height) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : ZMod height))
        (show yStart + h - 1 + 1 = yStart + h by omega)
  have hinside : ((((xStart + k : ℕ) : ZMod width),
      ((yStart + h - 1 : ℕ) : ZMod height)) : TorusVertex width height) ∈
      torusContiguousRectangle xStart yStart w h := by
    simp only [mem_torusContiguousRectangle,
      ZMod.val_natCast_of_lt (show xStart + k < width by omega),
      ZMod.val_natCast_of_lt (show yStart + h - 1 < height by omega)]
    omega
  have houtside : ((((xStart + k : ℕ) : ZMod width),
      ((yStart + h : ℕ) : ZMod height)) : TorusVertex width height) ∉
      torusContiguousRectangle xStart yStart w h := by
    simp only [mem_torusContiguousRectangle]
    exact fun hm => rectangle_interval_end_out yStart h hh hy hp ⟨hm.2.2.1, hm.2.2.2⟩
  unfold IsRegionBoundaryEdge torusUpEdge
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up
    ((xStart + k : ℕ) : ZMod width) ((yStart + h - 1 : ℕ) : ZMod height)) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hstep]
    exact Or.inl ⟨hinside, houtside⟩
  · rw [h1, h2, hstep]
    exact Or.inr ⟨houtside, hinside⟩

private theorem rectangle_boundary_down (xStart yStart w h : ℕ)
    (_hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hp : h < height) (k : ℕ) (hk : k < w) :
    IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart w h)
      (torusUpEdge (((xStart + k : ℕ) : ZMod width), (yStart : ZMod height) - 1)) := by
  have hinside : ((((xStart + k : ℕ) : ZMod width), (yStart : ZMod height)) :
      TorusVertex width height) ∈ torusContiguousRectangle xStart yStart w h := by
    simp only [mem_torusContiguousRectangle,
      ZMod.val_natCast_of_lt (show xStart + k < width by omega),
      ZMod.val_natCast_of_lt (show yStart < height by omega)]
    omega
  have houtside : ((((xStart + k : ℕ) : ZMod width), (yStart : ZMod height) - 1) :
      TorusVertex width height) ∉ torusContiguousRectangle xStart yStart w h := by
    simp only [mem_torusContiguousRectangle]
    exact fun hm => rectangle_interval_pred_out yStart h hh hy hp ⟨hm.2.2.1, hm.2.2.2⟩
  unfold IsRegionBoundaryEdge torusUpEdge
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up
    ((xStart + k : ℕ) : ZMod width) ((yStart : ZMod height) - 1)) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, sub_add_cancel]
    exact Or.inr ⟨houtside, hinside⟩
  · rw [h1, h2, sub_add_cancel]
    exact Or.inl ⟨hinside, houtside⟩

private theorem rectangle_boundary_right (xStart yStart w h : ℕ)
    (hw : 0 < w) (_hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hp : w < width) (k : ℕ) (hk : k < h) :
    IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart w h)
      (torusRightEdge (((xStart + w - 1 : ℕ) : ZMod width),
        ((yStart + k : ℕ) : ZMod height))) := by
  have hstep : (((xStart + w - 1 : ℕ) : ZMod width) + 1) =
      ((xStart + w : ℕ) : ZMod width) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : ZMod width))
        (show xStart + w - 1 + 1 = xStart + w by omega)
  have hinside : ((((xStart + w - 1 : ℕ) : ZMod width),
      ((yStart + k : ℕ) : ZMod height)) : TorusVertex width height) ∈
      torusContiguousRectangle xStart yStart w h := by
    simp only [mem_torusContiguousRectangle,
      ZMod.val_natCast_of_lt (show xStart + w - 1 < width by omega),
      ZMod.val_natCast_of_lt (show yStart + k < height by omega)]
    omega
  have houtside : ((((xStart + w : ℕ) : ZMod width),
      ((yStart + k : ℕ) : ZMod height)) : TorusVertex width height) ∉
      torusContiguousRectangle xStart yStart w h := by
    simp only [mem_torusContiguousRectangle]
    exact fun hm => rectangle_interval_end_out xStart w hw hx hp ⟨hm.1, hm.2.1⟩
  unfold IsRegionBoundaryEdge torusRightEdge
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right
    ((xStart + w - 1 : ℕ) : ZMod width) ((yStart + k : ℕ) : ZMod height)) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hstep]
    exact Or.inl ⟨hinside, houtside⟩
  · rw [h1, h2, hstep]
    exact Or.inr ⟨houtside, hinside⟩

private theorem rectangle_boundary_left (xStart yStart w h : ℕ)
    (hw : 0 < w) (_hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hp : w < width) (k : ℕ) (hk : k < h) :
    IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart w h)
      (torusRightEdge ((xStart : ZMod width) - 1, ((yStart + k : ℕ) : ZMod height))) := by
  have hinside : (((xStart : ZMod width), ((yStart + k : ℕ) : ZMod height)) :
      TorusVertex width height) ∈ torusContiguousRectangle xStart yStart w h := by
    simp only [mem_torusContiguousRectangle,
      ZMod.val_natCast_of_lt (show xStart < width by omega),
      ZMod.val_natCast_of_lt (show yStart + k < height by omega)]
    omega
  have houtside : (((xStart : ZMod width) - 1, ((yStart + k : ℕ) : ZMod height)) :
      TorusVertex width height) ∉ torusContiguousRectangle xStart yStart w h := by
    simp only [mem_torusContiguousRectangle]
    exact fun hm => rectangle_interval_pred_out xStart w hw hx hp ⟨hm.1, hm.2.1⟩
  unfold IsRegionBoundaryEdge torusRightEdge
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right
    ((xStart : ZMod width) - 1) ((yStart + k : ℕ) : ZMod height)) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, sub_add_cancel]
    exact Or.inr ⟨houtside, hinside⟩
  · rw [h1, h2, sub_add_cancel]
    exact Or.inl ⟨hinside, houtside⟩

/-- Every clockwise perimeter bond crosses the boundary of the actual
coordinate rectangle, including its possible seam bonds. -/
theorem torusRectanglePerimeterEdge_boundary (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hwp : w < width) (hhp : h < height) (i : Fin (2 * w + 2 * h)) :
    IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart w h)
      (torusRectanglePerimeterEdge (width := width) (height := height) xStart yStart w h i) := by
  unfold torusRectanglePerimeterEdge torusRectanglePerimeterCode
  split_ifs with ht hr hb
  · exact rectangle_boundary_up xStart yStart w h hw hh hx hy hhp i.val ht
  · exact rectangle_boundary_right xStart yStart w h hw hh hx hy hwp
      (w + h - 1 - i.val) (by omega)
  · exact rectangle_boundary_down xStart yStart w h hw hh hx hy hhp
      (2 * w + h - 1 - i.val) (by omega)
  · exact rectangle_boundary_left xStart yStart w h hw hh hx hy hwp
      (i.val - (2 * w + h)) (by omega)

private theorem rectangle_cast_eq_iff {n : ℕ} [NeZero n]
    {a b : ℕ} (ha : a < n) (hb : b < n) :
    (a : ZMod n) = (b : ZMod n) ↔ a = b := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hv
  · rintro rfl
    rfl

/-- No actual crossing bond is repeated by the clockwise numbering. -/
theorem torusRectanglePerimeterEdge_injective (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hwp : w < width) (hhp : h < height) :
    Function.Injective (torusRectanglePerimeterEdge (width := width) (height := height)
      xStart yStart w h) := by
  intro i j hij
  apply Fin.ext
  have he := torusEdgeEquiv.injective hij
  have hxs := rectangle_interval_last_ne_pred xStart w hw hx hwp
  have hys := rectangle_interval_last_ne_pred yStart h hh hy hhp
  unfold torusRectanglePerimeterCode at he
  split_ifs at he <;> simp only [Sum.inl.injEq, Sum.inr.injEq,
    Prod.mk.injEq] at he
  all_goals try exact (hxs he.1).elim
  all_goals try exact (hxs he.1.symm).elim
  all_goals try exact (hys he.2).elim
  all_goals try exact (hys he.2.symm).elim
  all_goals
    rcases he with ⟨he1, he2⟩
    try rw [rectangle_cast_eq_iff (by omega) (by omega)] at he1
    try rw [rectangle_cast_eq_iff (by omega) (by omega)] at he2
    omega

/-- The clockwise numbering is a bijection onto the actual crossing bonds.
Surjectivity uses the existing native rectangle perimeter cardinality. -/
noncomputable def torusRectanglePerimeterEquiv (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hwp : w < width) (hhp : h < height) :
    Fin (2 * w + 2 * h) ≃ {e : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart w h) e} :=
  Equiv.ofBijective
    (fun i => ⟨torusRectanglePerimeterEdge xStart yStart w h i,
      torusRectanglePerimeterEdge_boundary xStart yStart w h hw hh hx hy hwp hhp i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j hij
      exact torusRectanglePerimeterEdge_injective xStart yStart w h hw hh hx hy hwp hhp
        (congrArg Subtype.val hij), by
      rw [Fintype.card_fin,
        card_regionBoundaryEdge_torusRectangle xStart yStart w h hw hh hx hy hwp hhp]⟩)

@[simp] theorem torusRectanglePerimeterEquiv_apply_val (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hwp : w < width) (hhp : h < height) (i : Fin (2 * w + 2 * h)) :
    (torusRectanglePerimeterEquiv xStart yStart w h hw hh hx hy hwp hhp i).val =
      torusRectanglePerimeterEdge xStart yStart w h i := rfl

/-- The unique endpoint inside the rectangle of a clockwise crossing bond. -/
def torusRectanglePerimeterSite (xStart yStart w h : ℕ)
    (i : Fin (2 * w + 2 * h)) : TorusVertex width height :=
  if i.val < w then
    (((xStart + i.val : ℕ) : ZMod width), ((yStart + h - 1 : ℕ) : ZMod height))
  else if i.val < w + h then
    (((xStart + w - 1 : ℕ) : ZMod width),
      ((yStart + (w + h - 1 - i.val) : ℕ) : ZMod height))
  else if i.val < 2 * w + h then
    (((xStart + (2 * w + h - 1 - i.val) : ℕ) : ZMod width), (yStart : ZMod height))
  else
    ((xStart : ZMod width), ((yStart + (i.val - (2 * w + h)) : ℕ) : ZMod height))

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- Every enumerated boundary site belongs to the actual rectangle. -/
theorem torusRectanglePerimeterSite_mem (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (i : Fin (2 * w + 2 * h)) :
    torusRectanglePerimeterSite (width := width) (height := height) xStart yStart w h i ∈
      torusContiguousRectangle xStart yStart w h := by
  unfold torusRectanglePerimeterSite
  split_ifs <;> simp only [mem_torusContiguousRectangle]
  all_goals
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)]
    omega

/-- The outward native leg at an enumerated boundary site. -/
def torusRectanglePerimeterLeg (xStart yStart w h : ℕ)
    (i : Fin (2 * w + 2 * h)) :
    IncidentEdge (torusGraph width height) (torusRectanglePerimeterSite xStart yStart w h i) :=
  if i.val < w then torusTopLeg _
  else if i.val < w + h then torusRightLeg _
  else if i.val < 2 * w + h then torusDownLeg _
  else torusLeftLeg _

/-- The native leg of the interior site is precisely the enumerated actual
crossing bond. -/
@[simp] theorem torusRectanglePerimeterLeg_val (xStart yStart w h : ℕ)
    (i : Fin (2 * w + 2 * h)) :
    (torusRectanglePerimeterLeg (width := width) (height := height) xStart yStart w h i).val =
      torusRectanglePerimeterEdge xStart yStart w h i := by
  unfold torusRectanglePerimeterLeg torusRectanglePerimeterSite
    torusRectanglePerimeterEdge torusRectanglePerimeterCode
  by_cases ht : i.val < w <;> by_cases hr : i.val < w + h <;>
    by_cases hb : i.val < 2 * w + h <;> simp only [ht, hr, hb, ite_true, ite_false] <;>
    dsimp only [torusTopLeg, torusRightLeg, torusDownLeg, torusLeftLeg] <;>
    simp only [ht, hr, hb, ite_true, ite_false] <;> rfl

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- The perimeter corner coordinates lie in the closed rectangle. -/
theorem rectanglePerimeterCorner_le (w h : ℕ) (i : Fin (2 * w + 2 * h)) :
    (rectanglePerimeterCorner w h i).1 ≤ w ∧
      (rectanglePerimeterCorner w h i).2 ≤ h := by
  unfold rectanglePerimeterCorner
  split_ifs <;> dsimp only <;> omega

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- The cyclic perimeter visits each of its plaquette corners only once. -/
theorem rectanglePerimeterCorner_injective (w h : ℕ) (hw : 0 < w) (hh : 0 < h) :
    Function.Injective (rectanglePerimeterCorner w h) := by
  intro i j hij
  apply Fin.ext
  unfold rectanglePerimeterCorner at hij
  split_ifs at hij <;> simp only [Prod.mk.injEq] at hij <;> omega

/-- The actual torus plaquette corner at a clockwise boundary index.
The translation is in the torus, so corners on the period are included. -/
def torusRectanglePerimeterCorner (xStart yStart w h : ℕ)
    (i : Fin (2 * w + 2 * h)) : TorusVertex width height :=
  ((xStart : ZMod width) + ((rectanglePerimeterCorner w h i).1 : ZMod width),
    (yStart : ZMod height) + ((rectanglePerimeterCorner w h i).2 : ZMod height))

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- Proper rectangle side lengths keep all perimeter plaquette corners
separate even when the rectangle meets the coordinate seam. -/
theorem torusRectanglePerimeterCorner_injective (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hwp : w < width) (hhp : h < height) :
    Function.Injective (torusRectanglePerimeterCorner (width := width) (height := height)
      xStart yStart w h) := by
  intro i j hij
  apply rectanglePerimeterCorner_injective w h hw hh
  have hi := rectanglePerimeterCorner_le w h i
  have hj := rectanglePerimeterCorner_le w h j
  have h1 := add_left_cancel (congrArg Prod.fst hij)
  have h2 := add_left_cancel (congrArg Prod.snd hij)
  apply Prod.ext
  · exact (rectangle_cast_eq_iff (by omega) (by omega)).mp h1
  · exact (rectangle_cast_eq_iff (by omega) (by omega)).mp h2

end TNLean.PEPS
