/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusCut
import TNLean.PEPS.RegularWalkHolonomy

/-!
# Seam crossing numbers and actual torus closure holonomy

The two integer crossing numbers of a native walk count its oriented passages
through the horizontal and vertical seams. A rightward seam crossing contributes
`(1, 0)` and an upward seam crossing contributes `(0, 1)`. For commuting closure
elements `g, h`, a walk with crossing numbers `(n, m)` has actual transport
`h ^ n * (g⁻¹) ^ m`. Thus equality of these crossing numbers implies equality of
closure transports, without choosing a spanning tree or supplying a holonomy
relation.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`eq:2d:peps-with-ug-uh`, seam deformation in `eq:2d:move-strings`, lines
1622–1647, and the complement argument in the proof of Theorem 6.9, lines
1935–1990. The result concerns actual lattice walks. The existence of a walk in
the complement with prescribed crossing numbers is a separate geometric step.

**Scope restriction (simple torus graph):** Width and height are at least three,
as in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Oriented seam crossing numbers of an edge from its ordered tail to its
ordered head. Native rightward and upward seam edges have the reverse ordered
orientation. Source: SCP10, `eq:2d:peps-with-ug-uh`. -/
noncomputable def torusEdgeWinding (e : Edge (torusGraph width height)) : ℤ × ℤ :=
  match torusEdgeEquiv.symm e with
  | Sum.inl v => (if v.1 + 1 = 0 then -1 else 0, 0)
  | Sum.inr v => (0, if v.2 + 1 = 0 then -1 else 0)

/-- A directed passage through a seam has the sign of the direction in which
the walk crosses it. Source: SCP10, seam deformation, lines 1622–1647. -/
noncomputable def torusDirectedWinding {v w : TorusVertex width height}
    (h : (torusGraph width height).Adj v w) : ℤ × ℤ :=
  if v < w then torusEdgeWinding (Edge.ofAdj h) else -torusEdgeWinding (Edge.ofAdj h)

/-- The integer seam crossing numbers of an actual native torus walk.
Source: SCP10, complement cycle argument, lines 1935–1990. -/
noncomputable def torusWalkWinding {v w : TorusVertex width height} :
    (torusGraph width height).Walk v w → ℤ × ℤ
  | .nil => 0
  | .cons h p => torusWalkWinding p + torusDirectedWinding h

private theorem right_edge_winding (v : TorusVertex width height) :
    torusEdgeWinding (torusRightEdge v) = (if v.1 + 1 = 0 then -1 else 0, 0) := by
  unfold torusEdgeWinding
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (Sum.inl v)) with
    | Sum.inl z => (if z.1 + 1 = 0 then -1 else 0, 0)
    | Sum.inr z => (0, if z.2 + 1 = 0 then -1 else 0)) = _
  rw [Equiv.symm_apply_apply]

/-- A rightward seam passage has positive horizontal crossing number.
Source: SCP10, `eq:2d:peps-with-ug-uh` and `eq:2d:move-strings`. -/
theorem torusDirectedWinding_right (v : TorusVertex width height) :
    torusDirectedWinding (torusGraph_adj_right v.1 v.2) =
      (if v.1 + 1 = 0 then 1 else 0, 0) := by
  unfold torusDirectedWinding
  change (if v < (v.1 + 1, v.2) then torusEdgeWinding (torusRightEdge v)
    else -torusEdgeWinding (torusRightEdge v)) = _
  rw [right_edge_winding]
  by_cases hv : v.1 + 1 = 0
  · have hlt : ¬v < (v.1 + 1, v.2) := by
      intro h
      have hh := torusRightEdge_head_of_wrap v hv
      rw [torusRightEdge, Edge.ofAdj_of_lt (torusGraph_adj_right v.1 v.2) h] at hh
      exact (ne_of_lt h) hh.symm
    simp only [ite_eq_right hlt, ite_eq_left hv, Prod.neg_mk, neg_neg, neg_zero]
  · simp [hv]

private theorem up_edge_winding (v : TorusVertex width height) :
    torusEdgeWinding (torusUpEdge v) = (0, if v.2 + 1 = 0 then -1 else 0) := by
  unfold torusEdgeWinding
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (Sum.inr v)) with
    | Sum.inl z => (if z.1 + 1 = 0 then -1 else 0, 0)
    | Sum.inr z => (0, if z.2 + 1 = 0 then -1 else 0)) = _
  rw [Equiv.symm_apply_apply]

/-- An upward seam passage has positive vertical crossing number. Its closure
operator is consequently `g⁻¹`. Source: SCP10, `eq:2d:peps-with-ug-uh`. -/
theorem torusDirectedWinding_up (v : TorusVertex width height) :
    torusDirectedWinding (torusGraph_adj_up v.1 v.2) =
      (0, if v.2 + 1 = 0 then 1 else 0) := by
  unfold torusDirectedWinding
  change (if v < (v.1, v.2 + 1) then torusEdgeWinding (torusUpEdge v)
    else -torusEdgeWinding (torusUpEdge v)) = _
  rw [up_edge_winding]
  by_cases hv : v.2 + 1 = 0
  · have hlt : ¬v < (v.1, v.2 + 1) := by
      intro h
      have hh := torusUpEdge_head_of_wrap v hv
      rw [torusUpEdge, Edge.ofAdj_of_lt (torusGraph_adj_up v.1 v.2) h] at hh
      exact (ne_of_lt h) hh.symm
    simp only [ite_eq_right hlt, ite_eq_left hv, Prod.neg_mk, neg_neg, neg_zero]
  · simp [hv]

/-- Reversing a directed passage negates both seam crossing numbers. -/
theorem torusDirectedWinding_symm {v w : TorusVertex width height}
    (a : (torusGraph width height).Adj v w) :
    torusDirectedWinding a.symm = -torusDirectedWinding a := by
  unfold torusDirectedWinding
  rcases lt_or_gt_of_ne a.ne with hvw | hwv
  · simp only [ite_eq_left hvw, ite_eq_right (not_lt.mpr hvw.le),
      Edge.ofAdj_of_lt a hvw, Edge.ofAdj_of_gt a.symm hvw]
  · simp only [ite_eq_left hwv, ite_eq_right (not_lt.mpr hwv.le),
      Edge.ofAdj_of_gt a hwv, Edge.ofAdj_of_lt a.symm hwv, neg_neg]

/-- Concatenating actual walks adds their seam crossing numbers. -/
theorem torusWalkWinding_append {v w z : TorusVertex width height}
    (p : (torusGraph width height).Walk v w) (q : (torusGraph width height).Walk w z) :
    torusWalkWinding (p.append q) = torusWalkWinding p + torusWalkWinding q := by
  induction p with
  | nil => simp [torusWalkWinding]
  | cons a p ih =>
    simp only [SimpleGraph.Walk.cons_append, torusWalkWinding, ih]
    exact add_right_comm _ _ _

/-- Reversing an actual walk negates its seam crossing numbers. -/
theorem torusWalkWinding_reverse {v w : TorusVertex width height}
    (p : (torusGraph width height).Walk v w) :
    torusWalkWinding p.reverse = -torusWalkWinding p := by
  induction p with
  | nil => simp [torusWalkWinding]
  | cons a p ih =>
    rw [SimpleGraph.Walk.reverse_cons, torusWalkWinding_append, ih]
    simp only [torusWalkWinding, zero_add, neg_add]
    rw [torusDirectedWinding_symm]

variable {G : Type*} [Group G]

private theorem closure_edge (g h : G) (e : Edge (torusGraph width height)) :
    torusClosureEdgeAssignment g h e =
      h ^ (torusEdgeWinding e).1 * (g⁻¹) ^ (torusEdgeWinding e).2 := by
  unfold torusClosureEdgeAssignment torusEdgeWinding
  cases torusEdgeEquiv.symm e with
  | inl v =>
    simp [torusHorizontalClosureElement, apply_ite Inv.inv]
  | inr v =>
    simp [torusVerticalClosureElement]

private theorem closure_directed (g h : G) (hgh : Commute g h)
    {v w : TorusVertex width height} (a : (torusGraph width height).Adj v w) :
    regularDirectedTransport (torusClosureEdgeAssignment g h) a =
      h ^ (torusDirectedWinding a).1 * (g⁻¹) ^ (torusDirectedWinding a).2 := by
  unfold regularDirectedTransport torusDirectedWinding
  split_ifs with hvw
  · exact closure_edge g h _
  · rw [closure_edge]
    simp only [Prod.fst_neg, Prod.snd_neg, zpow_neg, mul_inv_rev]
    exact ((hgh.symm.inv_right.zpow_zpow _ _).inv_inv).symm.eq

/-- Actual closure transport is determined by the oriented seam crossing
numbers. Source: SCP10, `eq:2d:move-strings` and proof of Theorem 6.9,
lines 1935–1990. -/
theorem regularWalkHolonomy_torusClosureEdgeAssignment (g h : G) (hgh : Commute g h)
    {v w : TorusVertex width height} (p : (torusGraph width height).Walk v w) :
    regularWalkHolonomy (torusClosureEdgeAssignment g h) p =
      h ^ (torusWalkWinding p).1 * (g⁻¹) ^ (torusWalkWinding p).2 := by
  induction p with
  | nil => simp [torusWalkWinding]
  | cons a p ih =>
    rw [regularWalkHolonomy_cons, ih, closure_directed g h hgh]
    simp only [torusWalkWinding, Prod.fst_add, Prod.snd_add, zpow_add]
    exact (hgh.inv_left.zpow_zpow _ _).mul_mul_mul_comm _ _

/-- Equal integer seam crossing numbers give equal actual closure transports.
Source: SCP10, seam deformation and complement argument, lines 1622–1647 and
1935–1990. The walks may have different endpoints. -/
theorem regularWalkHolonomy_torusClosure_eq_of_winding_eq (g h : G) (hgh : Commute g h)
    {v w v' w' : TorusVertex width height}
    (p : (torusGraph width height).Walk v w) (q : (torusGraph width height).Walk v' w')
    (hpq : torusWalkWinding p = torusWalkWinding q) :
    regularWalkHolonomy (torusClosureEdgeAssignment g h) p =
      regularWalkHolonomy (torusClosureEdgeAssignment g h) q := by
  simp only [regularWalkHolonomy_torusClosureEdgeAssignment g h hgh, hpq]

end TNLean.PEPS
