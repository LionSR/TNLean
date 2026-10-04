/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRectangleConnectivity
import TNLean.PEPS.TorusSiteTensor

/-!
# Crossing-bond count for native torus rectangles

A positive bounded coordinate rectangle, with each side shorter than the
corresponding torus period, has twice its horizontal side length plus twice
its vertical side length in crossing bonds. Coordinate intervals may meet
the zero column or row and may end at the corresponding period; the cyclic
seam contributes the missing side in those cases.

**Scope restriction (simple torus graph):** Both torus periods are at least
three, so native bonds are distinct graph edges; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, rectangular blocks
in the boundary construction, local source lines 1935–1957 and 2043–2076.
-/

namespace TNLean.PEPS

private theorem crossing_symm (p q : Prop) :
    ((p ∧ ¬q) ∨ (¬p ∧ q)) ↔ ((q ∧ ¬p) ∨ (¬q ∧ p)) := by tauto

private theorem crossing_common_right (p q r : Prop) :
    (((p ∧ r) ∧ ¬(q ∧ r)) ∨ (¬(p ∧ r) ∧ (q ∧ r))) ↔
      (((p ∧ ¬q) ∨ (¬p ∧ q)) ∧ r) := by tauto

private theorem crossing_common_left (p q r : Prop) :
    (((p ∧ q) ∧ ¬(p ∧ r)) ∨ (¬(p ∧ q) ∧ (p ∧ r))) ↔
      (p ∧ ((q ∧ ¬r) ∨ (¬q ∧ r))) := by tauto

private theorem cyclic_interval_crossing_iff
    {n : ℕ} [NeZero n] [Fact (1 < n)] (a : ZMod n)
    (s l : ℕ) (hl : 0 < l) (hbound : s + l ≤ n) (hlen : l < n) :
    ((s ≤ a.val ∧ a.val < s + l) ∧ ¬(s ≤ (a + 1).val ∧ (a + 1).val < s + l) ∨
      ¬(s ≤ a.val ∧ a.val < s + l) ∧ (s ≤ (a + 1).val ∧ (a + 1).val < s + l)) ↔
      a.val = (if s = 0 then n - 1 else s - 1) ∨ a.val = s + l - 1 := by
  have ha := ZMod.val_lt a
  by_cases hstep : a.val + 1 < n
  · have hv : (a + 1).val = a.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hstep]
    rw [hv]
    split_ifs <;> omega
  · have hv : (a + 1).val = 0 := by
      rw [ZMod.val_add, ZMod.val_one]
      have he : a.val + 1 = n := by omega
      rw [he, Nat.mod_self]
    rw [hv]
    split_ifs <;> omega

private noncomputable def cyclicIntervalEquivFin
    {n : ℕ} [NeZero n] (s l : ℕ) (hbound : s + l ≤ n) :
    {a : ZMod n // s ≤ a.val ∧ a.val < s + l} ≃ Fin l where
  toFun a := ⟨a.1.val - s, by have := a.2; omega⟩
  invFun i := ⟨((s + i.val : ℕ) : ZMod n), by
    rw [ZMod.val_natCast_of_lt (show s + i.val < n by omega)]
    omega⟩
  left_inv a := by
    apply Subtype.ext
    apply ZMod.val_injective n
    simp only [ZMod.val_natCast_of_lt (show s + (a.1.val - s) < n by
      have := a.2; have := ZMod.val_lt a.1; omega)]
    have := a.2
    omega
  right_inv i := by
    apply Fin.ext
    simp only [ZMod.val_natCast_of_lt (show s + i.val < n by omega),
      Nat.add_sub_cancel_left]

private theorem card_cyclic_two_values
    {n : ℕ} [NeZero n] (a b : ℕ) (ha : a < n) (hb : b < n) (hne : a ≠ b) :
    Fintype.card {z : ZMod n // z.val = a ∨ z.val = b} = 2 := by
  classical
  have hset : Finset.univ.filter (fun z : ZMod n => z.val = a ∨ z.val = b) =
      {((a : ℕ) : ZMod n), ((b : ℕ) : ZMod n)} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (ZMod.val_injective n (by rw [h, ZMod.val_natCast_of_lt ha]))
      · exact Or.inr (ZMod.val_injective n (by rw [h, ZMod.val_natCast_of_lt hb]))
    · rintro (rfl | rfl)
      · exact Or.inl (ZMod.val_natCast_of_lt ha)
      · exact Or.inr (ZMod.val_natCast_of_lt hb)
  have hab : (a : ZMod n) ≠ (b : ZMod n) := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv
    exact hne hv
  rw [Fintype.card_subtype, hset]
  simp [hab]

private theorem card_cyclic_interval_endpoints
    {n : ℕ} [NeZero n] (s l : ℕ) (hl : 0 < l)
    (hbound : s + l ≤ n) (hlen : l < n) :
    Fintype.card {z : ZMod n // z.val = (if s = 0 then n - 1 else s - 1) ∨
      z.val = s + l - 1} = 2 := by
  apply card_cyclic_two_values
  · have := NeZero.pos n
    split_ifs <;> omega
  · omega
  · split_ifs <;> omega

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

private theorem boundary_torusRightEdge_rectangle_iff
    (xStart yStart xLen yLen : ℕ) (hxPos : 0 < xLen)
    (hxBound : xStart + xLen ≤ width) (hxLen : xLen < width)
    (v : TorusVertex width height) :
    IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen) (torusRightEdge v) ↔
      (v.1.val = (if xStart = 0 then width - 1 else xStart - 1) ∨
        v.1.val = xStart + xLen - 1) ∧
      (yStart ≤ v.2.val ∧ v.2.val < yStart + yLen) := by
  have he : IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen)
      (torusRightEdge v) ↔
      (v ∈ torusContiguousRectangle xStart yStart xLen yLen ∧
        (v.1 + 1, v.2) ∉ torusContiguousRectangle xStart yStart xLen yLen) ∨
      (v ∉ torusContiguousRectangle xStart yStart xLen yLen ∧
        (v.1 + 1, v.2) ∈ torusContiguousRectangle xStart yStart xLen yLen) := by
    unfold IsRegionBoundaryEdge torusRightEdge
    rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2]
    · simp only [h1, h2]
      exact crossing_symm _ _
  rw [he]
  have hm (p : TorusVertex width height) :
      p ∈ torusContiguousRectangle xStart yStart xLen yLen ↔
      (xStart ≤ p.1.val ∧ p.1.val < xStart + xLen) ∧
      (yStart ≤ p.2.val ∧ p.2.val < yStart + yLen) := by
    simp only [mem_torusContiguousRectangle, and_assoc]
  simp only [hm]
  rw [crossing_common_right, cyclic_interval_crossing_iff v.1 xStart xLen hxPos hxBound hxLen]

private theorem boundary_torusUpEdge_rectangle_iff
    (xStart yStart xLen yLen : ℕ) (hyPos : 0 < yLen)
    (hyBound : yStart + yLen ≤ height) (hyLen : yLen < height)
    (v : TorusVertex width height) :
    IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen) (torusUpEdge v) ↔
      (xStart ≤ v.1.val ∧ v.1.val < xStart + xLen) ∧
      (v.2.val = (if yStart = 0 then height - 1 else yStart - 1) ∨
        v.2.val = yStart + yLen - 1) := by
  have he : IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen)
      (torusUpEdge v) ↔
      (v ∈ torusContiguousRectangle xStart yStart xLen yLen ∧
        (v.1, v.2 + 1) ∉ torusContiguousRectangle xStart yStart xLen yLen) ∨
      (v ∉ torusContiguousRectangle xStart yStart xLen yLen ∧
        (v.1, v.2 + 1) ∈ torusContiguousRectangle xStart yStart xLen yLen) := by
    unfold IsRegionBoundaryEdge torusUpEdge
    rcases Edge.ofAdj_endpoints (torusGraph_adj_up v.1 v.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2]
    · simp only [h1, h2]
      exact crossing_symm _ _
  rw [he]
  have hm (p : TorusVertex width height) :
      p ∈ torusContiguousRectangle xStart yStart xLen yLen ↔
      (xStart ≤ p.1.val ∧ p.1.val < xStart + xLen) ∧
      (yStart ≤ p.2.val ∧ p.2.val < yStart + yLen) := by
    simp only [mem_torusContiguousRectangle, and_assoc]
  simp only [hm]
  rw [crossing_common_left, cyclic_interval_crossing_iff v.2 yStart yLen hyPos hyBound hyLen]

/-- There are twice the vertical side length in horizontal crossing bonds
of a positive bounded native rectangle whose horizontal side is shorter than
the period. Source: SCP10, rectangular boundary bonds, lines 1935–1957. -/
theorem card_horizontal_boundary_torusRectangle
    (xStart yStart xLen yLen : ℕ) (hxPos : 0 < xLen)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height)
    (hxLen : xLen < width) :
    Fintype.card {v : TorusVertex width height //
      IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen)
        (torusRightEdge v)} = 2 * yLen := by
  classical
  let e := (Equiv.subtypeEquivRight
    (boundary_torusRightEdge_rectangle_iff xStart yStart xLen yLen hxPos hxBound hxLen)).trans
    (Equiv.subtypeProdEquivProd
      (p := fun x : ZMod width =>
        x.val = (if xStart = 0 then width - 1 else xStart - 1) ∨ x.val = xStart + xLen - 1)
      (q := fun y : ZMod height => yStart ≤ y.val ∧ y.val < yStart + yLen))
  rw [Fintype.card_congr e, Fintype.card_prod,
    card_cyclic_interval_endpoints xStart xLen hxPos hxBound hxLen,
    Fintype.card_congr (cyclicIntervalEquivFin yStart yLen hyBound), Fintype.card_fin]

/-- There are twice the horizontal side length in vertical crossing bonds
of a positive bounded native rectangle whose vertical side is shorter than
the period. Source: SCP10, rectangular boundary bonds, lines 1935–1957. -/
theorem card_vertical_boundary_torusRectangle
    (xStart yStart xLen yLen : ℕ) (hyPos : 0 < yLen)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height)
    (hyLen : yLen < height) :
    Fintype.card {v : TorusVertex width height //
      IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen)
        (torusUpEdge v)} = 2 * xLen := by
  classical
  let e := (Equiv.subtypeEquivRight
    (boundary_torusUpEdge_rectangle_iff xStart yStart xLen yLen hyPos hyBound hyLen)).trans
    (Equiv.subtypeProdEquivProd
      (p := fun x : ZMod width => xStart ≤ x.val ∧ x.val < xStart + xLen)
      (q := fun y : ZMod height =>
        y.val = (if yStart = 0 then height - 1 else yStart - 1) ∨ y.val = yStart + yLen - 1))
  rw [Fintype.card_congr e, Fintype.card_prod,
    Fintype.card_congr (cyclicIntervalEquivFin xStart xLen hxBound), Fintype.card_fin,
    card_cyclic_interval_endpoints yStart yLen hyPos hyBound hyLen, Nat.mul_comm]

/-- The number of actual crossing bonds of a positive bounded coordinate
rectangle is its lattice perimeter. This includes rectangles meeting a zero
coordinate or ending at a torus period. Source: SCP10, rectangular blocks
in lines 1935–1957 and the boundary count in Corollary 6.10, lines 2074–2090. -/
theorem card_regionBoundaryEdge_torusRectangle
    (xStart yStart xLen yLen : ℕ) (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height)
    (hxLen : xLen < width) (hyLen : yLen < height) :
    Fintype.card {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen) f} =
      2 * xLen + 2 * yLen := by
  classical
  let R : Finset (TorusVertex width height) :=
    torusContiguousRectangle xStart yStart xLen yLen
  let e := Equiv.subtypeEquivOfSubtype (p := IsRegionBoundaryEdge R)
    (torusEdgeEquiv (width := width) (height := height))
  calc
    _ = Fintype.card {z : TorusVertex width height ⊕ TorusVertex width height //
        IsRegionBoundaryEdge R (torusEdgeEquiv z)} := (Fintype.card_congr e).symm
    _ = Fintype.card {v : TorusVertex width height //
        IsRegionBoundaryEdge R (torusRightEdge v)} +
        Fintype.card {v : TorusVertex width height //
          IsRegionBoundaryEdge R (torusUpEdge v)} := by
      rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
      rfl
    _ = _ := by
      rw [card_horizontal_boundary_torusRectangle
          xStart yStart xLen yLen hxPos hxBound hyBound hxLen,
        card_vertical_boundary_torusRectangle xStart yStart xLen yLen hyPos hxBound hyBound hyLen]
      omega

/-- A bounded positive square of side length `L` has `4 * L` actual crossing
bonds on a native torus with both periods greater than `L`.
Source: SCP10, rectangular boundary count in Corollary 6.10, lines 2074–2090. -/
theorem card_regionBoundaryEdge_torusSquare
    (xStart yStart L : ℕ) (hL : 0 < L)
    (hxBound : xStart + L ≤ width) (hyBound : yStart + L ≤ height)
    (hxLen : L < width) (hyLen : L < height) :
    Fintype.card {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart L L) f} = 4 * L := by
  rw [card_regionBoundaryEdge_torusRectangle xStart yStart L L hL hL hxBound hyBound hxLen hyLen]
  omega

private theorem card_horizontal_boundary_torusRectangle_le
    (xStart yStart xLen yLen : ℕ)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height) :
    Fintype.card {v : TorusVertex width height //
      IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen)
        (torusRightEdge v)} ≤ 2 * yLen := by
  classical
  by_cases hz : xLen = 0
  · have hR : torusContiguousRectangle (width := width) (height := height)
        xStart yStart xLen yLen = ∅ := by
      ext v
      simp only [mem_torusContiguousRectangle, Finset.notMem_empty, iff_false]
      omega
    simp [hR, IsRegionBoundaryEdge]
  · by_cases hlt : xLen < width
    · exact (card_horizontal_boundary_torusRectangle
        xStart yStart xLen yLen (by omega) hxBound hyBound hlt).le
    · have hx : xLen = width := by omega
      have hs : xStart = 0 := by omega
      have hn (v : TorusVertex width height) :
          ¬IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen)
            (torusRightEdge v) := by
        unfold IsRegionBoundaryEdge torusRightEdge
        rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          simp [h1, h2, mem_torusContiguousRectangle, hx, hs, ZMod.val_lt]
      rw [Fintype.card_eq_zero_iff.mpr ⟨fun v => hn v.1 v.2⟩]
      omega

private theorem card_vertical_boundary_torusRectangle_le
    (xStart yStart xLen yLen : ℕ)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height) :
    Fintype.card {v : TorusVertex width height //
      IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen)
        (torusUpEdge v)} ≤ 2 * xLen := by
  classical
  by_cases hz : yLen = 0
  · have hR : torusContiguousRectangle (width := width) (height := height)
        xStart yStart xLen yLen = ∅ := by
      ext v
      simp only [mem_torusContiguousRectangle, Finset.notMem_empty, iff_false]
      omega
    simp [hR, IsRegionBoundaryEdge]
  · by_cases hlt : yLen < height
    · exact (card_vertical_boundary_torusRectangle
        xStart yStart xLen yLen (by omega) hxBound hyBound hlt).le
    · have hy : yLen = height := by omega
      have hs : yStart = 0 := by omega
      have hn (v : TorusVertex width height) :
          ¬IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen)
            (torusUpEdge v) := by
        unfold IsRegionBoundaryEdge torusUpEdge
        rcases Edge.ofAdj_endpoints (torusGraph_adj_up v.1 v.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          simp [h1, h2, mem_torusContiguousRectangle, hy, hs, ZMod.val_lt]
      rw [Fintype.card_eq_zero_iff.mpr ⟨fun v => hn v.1 v.2⟩]
      omega

/-- Every bounded coordinate rectangle has at most its lattice perimeter in
crossing bonds, including empty rectangles and full coordinate bands.
Source: SCP10, rectangular boundary geometry in lines 1935–1957. -/
theorem card_regionBoundaryEdge_torusRectangle_le
    (xStart yStart xLen yLen : ℕ)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height) :
    Fintype.card {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart xLen yLen) f} ≤
      2 * xLen + 2 * yLen := by
  classical
  let R : Finset (TorusVertex width height) :=
    torusContiguousRectangle xStart yStart xLen yLen
  let e := Equiv.subtypeEquivOfSubtype (p := IsRegionBoundaryEdge R)
    (torusEdgeEquiv (width := width) (height := height))
  have hc : Fintype.card {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} =
      Fintype.card {v : TorusVertex width height // IsRegionBoundaryEdge R (torusRightEdge v)} +
      Fintype.card {v : TorusVertex width height // IsRegionBoundaryEdge R (torusUpEdge v)} := by
    rw [← Fintype.card_congr e, Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
    rfl
  rw [hc]
  have hright := card_horizontal_boundary_torusRectangle_le
    (width := width) (height := height) xStart yStart xLen yLen hxBound hyBound
  have hup := card_vertical_boundary_torusRectangle_le
    (width := width) (height := height) xStart yStart xLen yLen hxBound hyBound
  exact (Nat.add_le_add hright hup).trans_eq (Nat.add_comm _ _)

end TNLean.PEPS
