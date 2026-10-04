/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRectangleRegion
import TNLean.PEPS.TorusTranslationInvariant
import TNLean.PEPS.RegionBlock.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectivity and seam separation of torus rectangles

Removing the horizontal and vertical wrap bonds leaves an ordinary rectangular
grid on the native torus vertices. A coordinate rectangle whose two side lengths
are strictly smaller than the torus dimensions leaves at least one unused row
and one unused column. Each vertex of its complement can reach their intersection
along unused rows or columns. Thus the complement is connected without using
any seam bond. A positive bounded rectangle is itself connected in the same
grid. If its coordinate intervals lie strictly inside both coordinate ranges,
no wrap bond is incident to it. A left boundary edge witnesses that its boundary
is nonempty.

Motivation: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the rectangular
block and its surrounding stripes in `eq:iso:L-shape-scenario`, source lines
1935–1957. Those lines use this rectangular partition but state neither the
connectivity of the rectangle and its complement nor the seam exclusion. The
statements here are auxiliary combinatorial lemmas proved locally; they do not
replace the source's assertion for every topologically trivial block.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The native torus vertices joined only by nonwrapping consecutive coordinate
values. Source: SCP10, the common untwisted grid in lines 1935–1957. -/
def torusNonseamGraph (width height : ℕ) [NeZero width] [NeZero height] :
    SimpleGraph (TorusVertex width height) where
  Adj v w := (v.2 = w.2 ∧ (v.1.val + 1 = w.1.val ∨ w.1.val + 1 = v.1.val)) ∨
    (v.1 = w.1 ∧ (v.2.val + 1 = w.2.val ∨ w.2.val + 1 = v.2.val))
  symm := ⟨by
    intro v w h
    rcases h with ⟨hy, hx | hx⟩ | ⟨hx, hy | hy⟩
    · exact Or.inl ⟨hy.symm, Or.inr hx⟩
    · exact Or.inl ⟨hy.symm, Or.inl hx⟩
    · exact Or.inr ⟨hx.symm, Or.inr hy⟩
    · exact Or.inr ⟨hx.symm, Or.inl hy⟩⟩
  loopless := ⟨by intro v h; rcases h with ⟨_, h | h⟩ | ⟨_, h | h⟩ <;> omega⟩

instance : DecidableRel (torusNonseamGraph width height).Adj := by
  unfold torusNonseamGraph
  infer_instance

/-- Every nonseam grid edge is an actual torus edge. Source: SCP10,
`eq:iso:L-shape-scenario`, lines 1935–1957. -/
theorem torusNonseamGraph_le_torusGraph [Fact (1 < width)] [Fact (1 < height)] :
    torusNonseamGraph width height ≤ torusGraph width height := by
  intro v w h
  have hstep {n : ℕ} [NeZero n] (a b : ZMod n) (h : a.val + 1 = b.val) : a + 1 = b := by
    have hc := congrArg (fun k : ℕ => (k : ZMod n)) h
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using hc
  rcases h with ⟨hy, hx | hx⟩ | ⟨hx, hy | hy⟩
  · exact Or.inl ⟨hy, Or.inl (hstep _ _ hx)⟩
  · exact Or.inl ⟨hy, Or.inr (hstep _ _ hx)⟩
  · exact Or.inr ⟨hx, Or.inl (hstep _ _ hy)⟩
  · exact Or.inr ⟨hx, Or.inr (hstep _ _ hy)⟩

private theorem zmod_val_last_of_add_one_eq_zero {n : ℕ} [NeZero n]
    [Fact (1 < n)] (a : ZMod n) (ha : a + 1 = 0) : a.val + 1 = n := by
  have hval := ZMod.val_lt a
  have hc := congrArg ZMod.val ha
  rw [ZMod.val_add, ZMod.val_one, ZMod.val_zero] at hc
  by_contra h
  have hlt : a.val + 1 < n := by omega
  rw [Nat.mod_eq_of_lt hlt] at hc
  omega

private theorem nonseam_wrap_impossible {n : ℕ} [NeZero n]
    (hn : 2 < n) (a : ZMod n) (ha : a + 1 = 0) :
    ¬(a.val + 1 = (a + 1).val ∨ (a + 1).val + 1 = a.val) ∧ a ≠ a + 1 := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hlast := zmod_val_last_of_add_one_eq_zero a ha
  constructor
  · rw [ha, ZMod.val_zero]
    omega
  · intro heq
    have heqval := congrArg ZMod.val heq
    rw [ha, ZMod.val_zero] at heqval
    omega

/-- For width at least three, a horizontal wrap bond is absent from the
nonseam graph. Source: SCP10, closure seams in `eq:2d:peps-with-ug-uh`. -/
theorem torusNonseamGraph_not_horizontal_wrap (hw : 2 < width)
    (v : TorusVertex width height) (hwrap : v.1 + 1 = 0) :
    ¬(torusNonseamGraph width height).Adj v (v.1 + 1, v.2) := by
  have h := nonseam_wrap_impossible hw v.1 hwrap
  rintro (⟨_, hstep⟩ | ⟨heq, _⟩)
  · exact h.1 hstep
  · exact h.2 heq

/-- For height at least three, a vertical wrap bond is absent from the
nonseam graph. Source: SCP10, closure seams in `eq:2d:peps-with-ug-uh`. -/
theorem torusNonseamGraph_not_vertical_wrap (hh : 2 < height)
    (v : TorusVertex width height) (hwrap : v.2 + 1 = 0) :
    ¬(torusNonseamGraph width height).Adj v (v.1, v.2 + 1) := by
  have h := nonseam_wrap_impossible hh v.2 hwrap
  rintro (⟨heq, _⟩ | ⟨_, hstep⟩)
  · exact h.2 heq
  · exact h.1 hstep

private theorem reachable_fin_line {α : Type*} (Γ : SimpleGraph α) (n : ℕ) (hn : 0 < n)
    (f : Fin n → α)
    (hstep : ∀ (k : ℕ) (hk : k + 1 < n),
      Γ.Adj (f ⟨k, by omega⟩) (f ⟨k + 1, hk⟩)) (a b : Fin n) :
    Γ.Reachable (f a) (f b) := by
  have hr (k : ℕ) (hk : k < n) : Γ.Reachable (f ⟨0, hn⟩) (f ⟨k, hk⟩) := by
    induction k with
    | zero => exact .rfl
    | succ k ih => exact (ih (by omega)).trans (hstep k hk).reachable
  exact (hr a a.2).symm.trans (hr b b.2)

/-- The complement of a coordinate rectangle is connected using only
nonseam edges when both rectangle side lengths are strictly smaller than the
torus dimensions. Auxiliary lemma proved here, not stated in the source; motivated by
the rectangular partition of SCP10, lines 1935–1957. -/
theorem torusNonseamGraph_compl_rectangle_connected
    (xStart yStart xLen yLen : ℕ)
    (hxLen : xLen < width) (hyLen : yLen < height) :
    ((torusNonseamGraph width height).induce
      (↑((Finset.univ \ torusContiguousRectangle xStart yStart xLen yLen) :
        Finset (TorusVertex width height)) :
        Set (TorusVertex width height))).Connected := by
  classical
  let R : Finset (TorusVertex width height) :=
    torusContiguousRectangle xStart yStart xLen yLen
  let S := (↑(Finset.univ \ R) : Set (TorusVertex width height))
  let Γ := (torusNonseamGraph width height).induce S
  let cx := if xStart = 0 then xLen else 0
  let cy := if yStart = 0 then yLen else 0
  have hcx : cx < width ∧ ¬(xStart ≤ cx ∧ cx < xStart + xLen) := by
    dsimp [cx]; split_ifs <;> omega
  have hcy : cy < height ∧ ¬(yStart ≤ cy ∧ cy < yStart + yLen) := by
    dsimp [cy]; split_ifs <;> omega
  have hmem (x y : ℕ) (hx : x < width) (hy : y < height)
      (h : ¬(xStart ≤ x ∧ x < xStart + xLen ∧
        yStart ≤ y ∧ y < yStart + yLen)) :
      ((x : ZMod width), (y : ZMod height)) ∈ S := by
    simpa only [S, R, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      mem_torusContiguousRectangle, ZMod.val_natCast_of_lt hx,
      ZMod.val_natCast_of_lt hy] using h
  let anchor : S := ⟨((cx : ZMod width), (cy : ZMod height)),
    hmem cx cy hcx.1 hcy.1 (by omega)⟩
  have row (y : ℕ) (hy : y < height)
      (hout : ¬(yStart ≤ y ∧ y < yStart + yLen)) (a b : Fin width) :
      Γ.Reachable
        ⟨(((a : ℕ) : ZMod width), (y : ZMod height)), hmem a y a.2 hy (by omega)⟩
        ⟨(((b : ℕ) : ZMod width), (y : ZMod height)), hmem b y b.2 hy (by omega)⟩ := by
    apply reachable_fin_line Γ width (NeZero.pos width)
      (fun a => ⟨(((a : ℕ) : ZMod width), (y : ZMod height)),
        hmem a y a.2 hy (by omega)⟩)
    intro k hk
    exact Or.inl ⟨rfl, Or.inl (by
      change (k : ZMod width).val + 1 = ((k + 1 : ℕ) : ZMod width).val
      simp only [ZMod.val_natCast_of_lt (show k < width by omega),
        ZMod.val_natCast_of_lt hk])⟩
  have col (x : ℕ) (hx : x < width)
      (hout : ¬(xStart ≤ x ∧ x < xStart + xLen)) (a b : Fin height) :
      Γ.Reachable
        ⟨((x : ZMod width), ((a : ℕ) : ZMod height)), hmem x a hx a.2 (by omega)⟩
        ⟨((x : ZMod width), ((b : ℕ) : ZMod height)), hmem x b hx b.2 (by omega)⟩ := by
    apply reachable_fin_line Γ height (NeZero.pos height)
      (fun a => ⟨((x : ZMod width), ((a : ℕ) : ZMod height)),
        hmem x a hx a.2 (by omega)⟩)
    intro k hk
    exact Or.inr ⟨rfl, Or.inl (by
      change (k : ZMod height).val + 1 = ((k + 1 : ℕ) : ZMod height).val
      simp only [ZMod.val_natCast_of_lt (show k < height by omega),
        ZMod.val_natCast_of_lt hk])⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable Γ).mpr
  refine ⟨anchor, fun v => ?_⟩
  have hv : ¬(xStart ≤ v.1.1.val ∧ v.1.1.val < xStart + xLen ∧
      yStart ≤ v.1.2.val ∧ v.1.2.val < yStart + yLen) := by
    simpa only [S, R, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      mem_torusContiguousRectangle] using v.2
  have hx := ZMod.val_lt v.1.1
  have hy := ZMod.val_lt v.1.2
  by_cases hOutX : ¬(xStart ≤ v.1.1.val ∧ v.1.1.val < xStart + xLen)
  · have hr := row cy hcy.1 hcy.2 ⟨cx, hcx.1⟩ ⟨v.1.1.val, hx⟩
    have hc := col v.1.1.val hx hOutX ⟨cy, hcy.1⟩ ⟨v.1.2.val, hy⟩
    simpa only [ZMod.natCast_zmod_val] using hr.trans hc
  · have hOutY : ¬(yStart ≤ v.1.2.val ∧ v.1.2.val < yStart + yLen) := by omega
    have hc := col cx hcx.1 hcx.2 ⟨cy, hcy.1⟩ ⟨v.1.2.val, hy⟩
    have hr := row v.1.2.val hy hOutY ⟨cx, hcx.1⟩ ⟨v.1.1.val, hx⟩
    simpa only [ZMod.natCast_zmod_val] using hc.trans hr


/-- The same rectangle complement is connected in the actual torus graph.
Auxiliary lemma proved here, not stated in the source; motivated by the rectangular
partition of SCP10, lines 1935–1957. -/
theorem torusGraph_compl_rectangle_connected [Fact (1 < width)] [Fact (1 < height)]
    (xStart yStart xLen yLen : ℕ) (hxLen : xLen < width) (hyLen : yLen < height) :
    ((torusGraph width height).induce
      (↑((Finset.univ \ torusContiguousRectangle xStart yStart xLen yLen) :
        Finset (TorusVertex width height)) : Set (TorusVertex width height))).Connected := by
  exact (torusNonseamGraph_compl_rectangle_connected xStart yStart xLen yLen hxLen hyLen).mono
    (fun _ _ h => torusNonseamGraph_le_torusGraph h)


/-- A positive-length bounded coordinate rectangle is connected without using
wrap bonds. Auxiliary lemma proved here, not stated in the source; motivated by the
rectangular block of SCP10, lines 1935–1957. -/
theorem torusNonseamGraph_rectangle_connected (xStart yStart xLen yLen : ℕ)
    (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height) :
    ((torusNonseamGraph width height).induce
      (↑(torusContiguousRectangle xStart yStart xLen yLen :
        Finset (TorusVertex width height)) : Set (TorusVertex width height))).Connected := by
  classical
  let R := (↑(torusContiguousRectangle xStart yStart xLen yLen :
    Finset (TorusVertex width height)) : Set (TorusVertex width height))
  let Γ := (torusNonseamGraph width height).induce R
  have hmem (x : Fin xLen) (y : Fin yLen) :
      (((xStart + x : ℕ) : ZMod width), ((yStart + y : ℕ) : ZMod height)) ∈ R := by
    have hx : xStart + x.val < width := by omega
    have hy : yStart + y.val < height := by omega
    simp only [R, Finset.mem_coe, mem_torusContiguousRectangle,
      ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy]
    omega
  let vertex (x : Fin xLen) (y : Fin yLen) : R :=
    ⟨(((xStart + x : ℕ) : ZMod width), ((yStart + y : ℕ) : ZMod height)), hmem x y⟩
  have row (y : Fin yLen) (a b : Fin xLen) :
      Γ.Reachable (vertex a y) (vertex b y) := by
    apply reachable_fin_line Γ xLen hxPos (fun x => vertex x y)
    intro k hk
    exact Or.inl ⟨rfl, Or.inl (by
      change ((xStart + k : ℕ) : ZMod width).val + 1 =
        ((xStart + (k + 1) : ℕ) : ZMod width).val
      rw [ZMod.val_natCast_of_lt (show xStart + k < width by omega),
        ZMod.val_natCast_of_lt (show xStart + (k + 1) < width by omega)]
      omega)⟩
  have col (x : Fin xLen) (a b : Fin yLen) :
      Γ.Reachable (vertex x a) (vertex x b) := by
    apply reachable_fin_line Γ yLen hyPos (fun y => vertex x y)
    intro k hk
    exact Or.inr ⟨rfl, Or.inl (by
      change ((yStart + k : ℕ) : ZMod height).val + 1 =
        ((yStart + (k + 1) : ℕ) : ZMod height).val
      rw [ZMod.val_natCast_of_lt (show yStart + k < height by omega),
        ZMod.val_natCast_of_lt (show yStart + (k + 1) < height by omega)]
      omega)⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable Γ).mpr
  refine ⟨vertex ⟨0, hxPos⟩ ⟨0, hyPos⟩, fun v => ?_⟩
  have hv : xStart ≤ v.1.1.val ∧ v.1.1.val < xStart + xLen ∧
      yStart ≤ v.1.2.val ∧ v.1.2.val < yStart + yLen := by
    simpa only [R, Finset.mem_coe, mem_torusContiguousRectangle] using v.2
  let x : Fin xLen := ⟨v.1.1.val - xStart, by omega⟩
  let y : Fin yLen := ⟨v.1.2.val - yStart, by omega⟩
  have heq : vertex x y = v := by
    apply Subtype.ext
    dsimp [vertex, x, y]
    rw [Nat.add_sub_of_le hv.1, Nat.add_sub_of_le hv.2.2.1,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [← heq]
  exact (row ⟨0, hyPos⟩ ⟨0, hxPos⟩ x).trans (col x ⟨0, hyPos⟩ y)

/-- The positive bounded rectangle is connected in the actual torus graph.
Auxiliary lemma proved here, not stated in the source; motivated by the rectangular
block of SCP10, lines 1935–1957. -/
theorem torusGraph_rectangle_connected [Fact (1 < width)] [Fact (1 < height)]
    (xStart yStart xLen yLen : ℕ) (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height) :
    ((torusGraph width height).induce
      (↑(torusContiguousRectangle xStart yStart xLen yLen :
        Finset (TorusVertex width height)) : Set (TorusVertex width height))).Connected := by
  exact (torusNonseamGraph_rectangle_connected
    xStart yStart xLen yLen hxPos hyPos hxBound hyBound).mono
    (fun _ _ h => torusNonseamGraph_le_torusGraph h)

/-- A horizontal wrap bond has no endpoint in a strictly interior coordinate
rectangle. Auxiliary lemma proved here; motivated by the closure seams surrounding
the block in SCP10, lines 1935–1957. -/
theorem torusRightEdge_not_incident_rectangle_of_wrap
    [Fact (1 < width)] [Fact (1 < height)]
    (xStart yStart xLen yLen : ℕ) (hxStart : 0 < xStart)
    (hxEnd : xStart + xLen < width) (v : TorusVertex width height)
    (hwrap : v.1 + 1 = 0) :
    ¬IsRegionIncidentEdge (torusContiguousRectangle xStart yStart xLen yLen)
      (torusRightEdge v) := by
  have hlast := zmod_val_last_of_add_one_eq_zero v.1 hwrap
  have h₁ : v ∉ torusContiguousRectangle xStart yStart xLen yLen := by
    simp only [mem_torusContiguousRectangle]
    omega
  have h₂ : (v.1 + 1, v.2) ∉ torusContiguousRectangle xStart yStart xLen yLen := by
    simp only [mem_torusContiguousRectangle, hwrap, ZMod.val_zero]
    omega
  unfold IsRegionIncidentEdge torusRightEdge
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    simp only [ha, hb, h₁, h₂, or_self, not_false_eq_true]

/-- A vertical wrap bond has no endpoint in a strictly interior coordinate
rectangle. Auxiliary lemma proved here; motivated by the closure seams surrounding
the block in SCP10, lines 1935–1957. -/
theorem torusUpEdge_not_incident_rectangle_of_wrap
    [Fact (1 < width)] [Fact (1 < height)]
    (xStart yStart xLen yLen : ℕ) (hyStart : 0 < yStart)
    (hyEnd : yStart + yLen < height) (v : TorusVertex width height)
    (hwrap : v.2 + 1 = 0) :
    ¬IsRegionIncidentEdge (torusContiguousRectangle xStart yStart xLen yLen)
      (torusUpEdge v) := by
  have hlast := zmod_val_last_of_add_one_eq_zero v.2 hwrap
  have h₁ : v ∉ torusContiguousRectangle xStart yStart xLen yLen := by
    simp only [mem_torusContiguousRectangle]
    omega
  have h₂ : (v.1, v.2 + 1) ∉ torusContiguousRectangle xStart yStart xLen yLen := by
    simp only [mem_torusContiguousRectangle, hwrap, ZMod.val_zero]
    omega
  unfold IsRegionIncidentEdge torusUpEdge
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up v.1 v.2) with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    simp only [ha, hb, h₁, h₂, or_self, not_false_eq_true]


/-- A positive bounded rectangle with a nonzero starting column has an actual
left boundary edge. Auxiliary lemma proved here; motivated by the boundary bonds of
the block in SCP10, lines 1935–1957. -/
theorem nonempty_boundaryEdge_torusRectangle
    [Fact (1 < width)] [Fact (1 < height)]
    (xStart yStart xLen yLen : ℕ) (hxStart : 0 < xStart)
    (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height) :
    Nonempty {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen) f} := by
  let v : TorusVertex width height :=
    (((xStart - 1 : ℕ) : ZMod width), (yStart : ZMod height))
  have hs : v.1 + 1 = (xStart : ZMod width) := by
    change ((xStart - 1 : ℕ) : ZMod width) + 1 = (xStart : ZMod width)
    have hnat : xStart - 1 + 1 = xStart := Nat.sub_add_cancel (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : ZMod width)) hnat
  have h₁ : v ∉ torusContiguousRectangle xStart yStart xLen yLen := by
    simp only [mem_torusContiguousRectangle, v,
      ZMod.val_natCast_of_lt (show xStart - 1 < width by omega),
      ZMod.val_natCast_of_lt (show yStart < height by omega)]
    omega
  have h₂ : (v.1 + 1, v.2) ∈ torusContiguousRectangle xStart yStart xLen yLen := by
    simp only [mem_torusContiguousRectangle, hs, v,
      ZMod.val_natCast_of_lt (show xStart < width by omega),
      ZMod.val_natCast_of_lt (show yStart < height by omega)]
    omega
  refine ⟨⟨torusRightEdge v, ?_⟩⟩
  unfold IsRegionBoundaryEdge torusRightEdge
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    simp only [ha, hb, h₁, h₂, not_false_eq_true, not_true_eq_false, and_self,
      false_or, or_false]

end TNLean.PEPS
