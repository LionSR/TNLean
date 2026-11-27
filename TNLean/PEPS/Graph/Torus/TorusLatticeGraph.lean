/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

import TNLean.PEPS.Graph.Region.EdgeMapSubgraph

/-!
# The periodic (torus) lattice graph for the translation-invariant normal PEPS proof

The translationally invariant square-lattice theorem of the normal PEPS proof
(arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`) is stated on a lattice with **no boundary
and no preferred origin**: one tensor is repeated at every site, and translation
acts as a symmetry of the network. The finite model of such a lattice is the
discrete torus: the vertex set is `ZMod width × ZMod height` with cyclic
nearest-neighbour edges, on which the coordinate translations are graph
automorphisms (see `TNLean/PEPS/TorusTranslation.lean`).

The open rectangular model `QICLean/ManyBody/Sites/Lattice/Square.lean` has a boundary
that breaks translation: its boundary edges have no interior margin, so the
every-edge blocking construction only reaches interior edges
(`docs/paper-gaps/peps_normal_ft_section3_route.tex`, remaining obligation 4).
The torus removes the boundary, so on it every edge is interior and the
construction is complete (same note, remaining obligation 6). This file records
the torus geometry; the transport of the interior-edge blocking argument from
the open lattice onto the torus is a separate step.

The vertex coordinate ring `ZMod width` is finite and nontrivial exactly when
`1 < width`, recorded as the instances `[NeZero width]` (finiteness) and
`[Fact (1 < width)]` (nontriviality, hence no self-loops); likewise for the
vertical coordinate. The torus is genuinely a cycle in each direction precisely
under `1 < width` and `1 < height`, matching the source's large periodic lattice.

## Design note on the vertex linear order

The project-level `Edge` type orients an undirected edge by an ambient
`LinearOrder` on the vertices. We give `TorusVertex width height` the
lexicographic order through the coordinate value injection `v ↦ (v.1.val,
v.2.val)`, mirroring the open-lattice instance
(`ManyBody.instLinearOrderSquareLatticeVertex`). As there, the
`toDecidableEq` field is pinned to the canonical product decidable equality
`instDecidableEqProd` rather than the comparison-derived one that
`LinearOrder.lift'` would synthesize, so the geometry constructions over the
product decidable equality and the gauge constructions using the linear-order
decidable equality agree definitionally.

The file also records the edges of the torus named by their base vertex: the right
and up edges (`torusRightEdge`, `torusUpEdge`), the four legs of a vertex
(`torusTopLeg`, `torusRightLeg`, `torusDownLeg`, `torusLeftLeg`), and, when both
periods are at least three, the equivalence of the edges with two copies of the
vertices (`torusEdgeEquiv`) and the numbering of the incident edges of a vertex by its
four legs (`torusIncidentLegEquiv`).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open ManyBody (Edge)

namespace TNLean
namespace PEPS

/-- The vertex set of the discrete torus of size `width × height`: pairs of
periodic horizontal and vertical coordinates.  Translation acts on it by
coordinate addition (see `TNLean/PEPS/TorusTranslation.lean`).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the translationally invariant theorem
is set on a lattice on which translation is a symmetry. -/
abbrev TorusVertex (width height : ℕ) : Type :=
  ZMod width × ZMod height

instance instFintypeTorusVertex (width height : ℕ) [NeZero width] [NeZero height] :
    Fintype (TorusVertex width height) :=
  inferInstance

instance instDecidableEqTorusVertex (width height : ℕ) :
    DecidableEq (TorusVertex width height) :=
  inferInstance

/-- The torus coordinate value injection `v ↦ (v.1.val, v.2.val)` into the
lexicographic product of `ℕ` is injective, the witness for the lexicographic
linear order on `TorusVertex`. -/
theorem torusVertexValLex_injective (width height : ℕ) [NeZero width] [NeZero height] :
    Function.Injective
      (fun v : TorusVertex width height => toLex (v.1.val, v.2.val)) := by
  intro v w h
  have h' := ofLex_inj.mpr h
  simp only [ofLex_toLex, Prod.mk.injEq] at h'
  exact Prod.ext (ZMod.val_injective width h'.1) (ZMod.val_injective height h'.2)

/-- The torus vertex set is ordered lexicographically through the coordinate
value injection `v ↦ (v.1.val, v.2.val)`.  The project-level `Edge` type uses an
ambient linear order to orient undirected graph edges, so this instance lets the
torus graph use the same edge type as the general PEPS development.

The decidable-equality field is pinned to the canonical product decidable
equality `instDecidableEqProd` rather than the comparison-derived one that
`LinearOrder.lift'` would synthesize, exactly as for the open-lattice instance
`ManyBody.instLinearOrderSquareLatticeVertex`.  All other order fields are
taken from `LinearOrder.lift'`, so the lexicographic comparison is unchanged. -/
instance instLinearOrderTorusVertex (width height : ℕ) [NeZero width] [NeZero height] :
    LinearOrder (TorusVertex width height) := by
  classical
  exact
    let src : LinearOrder (TorusVertex width height) :=
      LinearOrder.lift'
        (fun v : TorusVertex width height => toLex (v.1.val, v.2.val))
        (torusVertexValLex_injective width height)
    @Function.Injective.linearOrder _ _ _ src.toLE src.toLT src.toMax src.toMin src.toOrd
      instDecidableEqProd src.toDecidableLE src.toDecidableLT
      (fun v : TorusVertex width height => toLex (v.1.val, v.2.val))
      (torusVertexValLex_injective width height)
      (le := Iff.rfl) (lt := Iff.rfl)
      (min := fun x y => by
        change (fun v : TorusVertex width height => toLex (v.1.val, v.2.val)) (src.min x y) = _
        rw [src.min_def]; split
        · rw [min_eq_left ‹_›]
        · rw [min_eq_right (not_le.mp ‹_›).le])
      (max := fun x y => by
        change (fun v : TorusVertex width height => toLex (v.1.val, v.2.val)) (src.max x y) = _
        rw [src.max_def]; split
        · rw [max_eq_right ‹_›]
        · rw [max_eq_left (not_le.mp ‹_›).le])
      (compare := fun _ _ => rfl)

/-- Horizontal nearest-neighbour relation on the torus: equal vertical coordinate
and horizontal coordinates differing by one, the difference taken cyclically in
`ZMod width`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`, where the edge blocking is applied to
horizontal and vertical lattice edges. -/
def torusHorizontalNeighbor {width height : ℕ}
    (v w : TorusVertex width height) : Prop :=
  v.2 = w.2 ∧ (v.1 + 1 = w.1 ∨ w.1 + 1 = v.1)

/-- Vertical nearest-neighbour relation on the torus: equal horizontal coordinate
and vertical coordinates differing by one, the difference taken cyclically in
`ZMod height`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusVerticalNeighbor {width height : ℕ}
    (v w : TorusVertex width height) : Prop :=
  v.1 = w.1 ∧ (v.2 + 1 = w.2 ∨ w.2 + 1 = v.2)

/-- The horizontal cyclic-neighbour relation is symmetric. -/
theorem torusHorizontalNeighbor_symm {width height : ℕ} {v w : TorusVertex width height}
    (h : torusHorizontalNeighbor v w) : torusHorizontalNeighbor w v :=
  ⟨h.1.symm, h.2.imp (·) (·) |>.elim Or.inr Or.inl⟩

/-- The vertical cyclic-neighbour relation is symmetric. -/
theorem torusVerticalNeighbor_symm {width height : ℕ} {v w : TorusVertex width height}
    (h : torusVerticalNeighbor v w) : torusVerticalNeighbor w v :=
  ⟨h.1.symm, h.2.imp (·) (·) |>.elim Or.inr Or.inl⟩

instance instDecidableTorusHorizontalNeighbor {width height : ℕ}
    (v w : TorusVertex width height) : Decidable (torusHorizontalNeighbor v w) := by
  unfold torusHorizontalNeighbor; infer_instance

instance instDecidableTorusVerticalNeighbor {width height : ℕ}
    (v w : TorusVertex width height) : Decidable (torusVerticalNeighbor v w) := by
  unfold torusVerticalNeighbor; infer_instance

/-- The discrete torus graph with cyclic nearest-neighbour horizontal and
vertical edges.  The nontriviality instances `[Fact (1 < width)]` and
`[Fact (1 < height)]` make `1 ≠ 0` in each coordinate ring, so a vertex is never
its own cyclic neighbour and the graph is loopless.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
`Papers/1804.04964/paper_normal.tex`, where the translationally invariant theorem
is set on a periodic lattice. -/
def torusGraph (width height : ℕ) [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] : SimpleGraph (TorusVertex width height) where
  Adj v w := torusHorizontalNeighbor v w ∨ torusVerticalNeighbor v w
  symm := ⟨by
    intro v w h
    rcases h with ⟨hy, hx | hx⟩ | ⟨hx, hy | hy⟩
    · exact Or.inl ⟨hy.symm, Or.inr hx⟩
    · exact Or.inl ⟨hy.symm, Or.inl hx⟩
    · exact Or.inr ⟨hx.symm, Or.inr hy⟩
    · exact Or.inr ⟨hx.symm, Or.inl hy⟩⟩
  loopless := by
    constructor
    intro v h
    rcases h with ⟨_, hx | hx⟩ | ⟨_, hy | hy⟩
    · exact one_ne_zero (α := ZMod width)
        (add_left_cancel (a := v.1) (b := (1 : ZMod width)) (c := 0) (by rw [add_zero]; exact hx))
    · exact one_ne_zero (α := ZMod width)
        (add_left_cancel (a := v.1) (b := (1 : ZMod width)) (c := 0) (by rw [add_zero]; exact hx))
    · exact one_ne_zero (α := ZMod height)
        (add_left_cancel (a := v.2) (b := (1 : ZMod height)) (c := 0) (by rw [add_zero]; exact hy))
    · exact one_ne_zero (α := ZMod height)
        (add_left_cancel (a := v.2) (b := (1 : ZMod height)) (c := 0) (by rw [add_zero]; exact hy))

instance instDecidableRelTorusGraphAdj (width height : ℕ) [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] :
    DecidableRel (torusGraph width height).Adj := by
  intro v w
  unfold torusGraph
  infer_instance

@[simp] theorem torusGraph_adj {width height : ℕ} [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] (v w : TorusVertex width height) :
    (torusGraph width height).Adj v w ↔
      torusHorizontalNeighbor v w ∨ torusVerticalNeighbor v w :=
  Iff.rfl

/-- A vertex and its cyclic right neighbour `(x + 1, y)` are adjacent.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem torusGraph_adj_right {width height : ℕ} [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] (x : ZMod width) (y : ZMod height) :
    (torusGraph width height).Adj (x, y) (x + 1, y) :=
  Or.inl ⟨rfl, Or.inl rfl⟩

/-- A vertex and its cyclic upper neighbour `(x, y + 1)` are adjacent.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem torusGraph_adj_up {width height : ℕ} [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] (x : ZMod width) (y : ZMod height) :
    (torusGraph width height).Adj (x, y) (x, y + 1) :=
  Or.inr ⟨rfl, Or.inl rfl⟩

/-! ### Orientation of torus edges

Each edge of the torus graph is horizontal or vertical, and no edge is both.  As
on the open lattice these orientation predicates split the per-edge data into the
two classes "described by the same horizontal matrix" and "described by the same
vertical matrix" of the source's translation-invariant reduction. -/

/-- An edge of the torus graph is **horizontal** when its endpoints are horizontal
cyclic neighbours.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def IsHorizontalTorusEdge {width height : ℕ} [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] (e : Edge (torusGraph width height)) : Prop :=
  torusHorizontalNeighbor e.1.1 e.1.2

/-- An edge of the torus graph is **vertical** when its endpoints are vertical
cyclic neighbours.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def IsVerticalTorusEdge {width height : ℕ} [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] (e : Edge (torusGraph width height)) : Prop :=
  torusVerticalNeighbor e.1.1 e.1.2

instance instDecidableIsHorizontalTorusEdge {width height : ℕ} [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] (e : Edge (torusGraph width height)) :
    Decidable (IsHorizontalTorusEdge e) := by
  unfold IsHorizontalTorusEdge; infer_instance

instance instDecidableIsVerticalTorusEdge {width height : ℕ} [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] (e : Edge (torusGraph width height)) :
    Decidable (IsVerticalTorusEdge e) := by
  unfold IsVerticalTorusEdge; infer_instance

/-- Every edge of the torus graph is horizontal or vertical.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem torusEdge_horizontal_or_vertical {width height : ℕ} [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] (e : Edge (torusGraph width height)) :
    IsHorizontalTorusEdge e ∨ IsVerticalTorusEdge e :=
  e.2.2

/-- No edge of the torus graph is both horizontal and vertical.  A horizontal edge
keeps the vertical coordinate fixed and shifts the horizontal one by one; a
vertical edge does the reverse.  If an edge were both, the horizontal coordinate
would be both fixed and shifted by one, forcing `1 = 0`, impossible by
nontriviality.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem torusEdge_not_horizontal_and_vertical {width height : ℕ} [NeZero width] [NeZero height]
    [Fact (1 < width)] [Fact (1 < height)] (e : Edge (torusGraph width height)) :
    ¬ (IsHorizontalTorusEdge e ∧ IsVerticalTorusEdge e) := by
  rintro ⟨hHorizontal, hVertical⟩
  have hxEq : e.1.1.1 = e.1.2.1 := hVertical.1
  rcases hHorizontal.2 with hStep | hStep
  · exact one_ne_zero (α := ZMod width)
      (add_left_cancel (a := e.1.1.1) (b := (1 : ZMod width)) (c := 0)
        (by rw [add_zero, hStep, ← hxEq]))
  · exact one_ne_zero (α := ZMod width)
      (add_left_cancel (a := e.1.2.1) (b := (1 : ZMod width)) (c := 0)
        (by rw [add_zero, hStep, hxEq]))

section RightAndUpEdges

variable {width height : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-! ### Normal form of horizontal and vertical torus edges

Each horizontal edge is the right edge of a well-defined left endpoint `p`, the
edge with unordered endpoints `p` and `p + (1, 0)`.  The lexicographic order may
place either of these first (the coordinate value wraps around the torus), so the
left endpoint is read from whichever incidence carries the `+1` step.  This normal
form gives the transitivity of the translation action on the horizontal class:
translating the left endpoint of one horizontal edge to the left
endpoint of another carries the whole edge across. -/

/-- The horizontal torus edge with left endpoint `p`, i.e. the edge on the adjacent
pair `(p, p + (1, 0))`. -/
def torusRightEdge (p : TorusVertex width height) : Edge (torusGraph width height) :=
  ManyBody.Edge.ofAdj (torusGraph_adj_right p.1 p.2)

/-- The vertical torus edge with lower endpoint `p`, i.e. the edge on the adjacent
pair `(p, p + (0, 1))`. -/
def torusUpEdge (p : TorusVertex width height) : Edge (torusGraph width height) :=
  ManyBody.Edge.ofAdj (torusGraph_adj_up p.1 p.2)

/-- Every horizontal torus edge is the right edge of a left endpoint `p`: its
unordered endpoints are `p` and `p + (1, 0)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isHorizontalTorusEdge_eq_rightEdge {e : Edge (torusGraph width height)}
    (he : IsHorizontalTorusEdge e) :
    ∃ p : TorusVertex width height, e = torusRightEdge p := by
  have hc : e.1.1.2 = e.1.2.2 := he.1
  rcases he.2 with h2 | h2
  · refine ⟨e.1.1, ?_⟩
    rw [torusRightEdge]
    symm
    apply ManyBody.Edge.ofAdj_eq_of_endpoints
    exact Or.inl ⟨rfl, Prod.ext (by exact h2) (by simpa using hc)⟩
  · refine ⟨e.1.2, ?_⟩
    rw [torusRightEdge]
    symm
    apply ManyBody.Edge.ofAdj_eq_of_endpoints
    exact Or.inr ⟨rfl, Prod.ext (by exact h2) (by simpa using hc.symm)⟩

/-- Every vertical torus edge is the up edge of a lower endpoint `p`: its unordered
endpoints are `p` and `p + (0, 1)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isVerticalTorusEdge_eq_upEdge {e : Edge (torusGraph width height)}
    (he : IsVerticalTorusEdge e) :
    ∃ p : TorusVertex width height, e = torusUpEdge p := by
  have hc : e.1.1.1 = e.1.2.1 := he.1
  rcases he.2 with h2 | h2
  · refine ⟨e.1.1, ?_⟩
    rw [torusUpEdge]
    symm
    apply ManyBody.Edge.ofAdj_eq_of_endpoints
    exact Or.inl ⟨rfl, Prod.ext (by simpa using hc) (by exact h2)⟩
  · refine ⟨e.1.2, ?_⟩
    rw [torusUpEdge]
    symm
    apply ManyBody.Edge.ofAdj_eq_of_endpoints
    exact Or.inr ⟨rfl, Prod.ext (by simpa using hc.symm) (by exact h2)⟩

/-! ### Orientation and injectivity of right and up edges -/

/-- A right edge is horizontal. -/
theorem isHorizontalTorusEdge_torusRightEdge (p : TorusVertex width height) :
    IsHorizontalTorusEdge (torusRightEdge p) := by
  unfold IsHorizontalTorusEdge torusRightEdge
  rcases ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2]
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

/-- An up edge is vertical. -/
theorem isVerticalTorusEdge_torusUpEdge (p : TorusVertex width height) :
    IsVerticalTorusEdge (torusUpEdge p) := by
  unfold IsVerticalTorusEdge torusUpEdge
  rcases ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2]
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

/-- In `ZMod n` with `2 < n`, no two elements are each the successor of the other. -/
theorem zmod_not_add_one_eq_and_add_one_eq {n : ℕ} [Fact (2 < n)] (x y : ZMod n) :
    ¬ (x = y + 1 ∧ x + 1 = y) := by
  rintro ⟨h1, h2⟩
  have h : ((2 : ℕ) : ZMod n) = 0 := by
    calc ((2 : ℕ) : ZMod n) = (y + 1 + 1) - y := by push_cast; ring
      _ = 0 := by rw [← h1, h2, sub_self]
  have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 n).mp h)
  exact absurd (Fact.out : 2 < n) (not_lt.mpr this)

/-- On a torus of width at least three, distinct vertices have distinct right edges. -/
theorem torusRightEdge_injective [Fact (2 < width)] :
    Function.Injective (torusRightEdge (width := width) (height := height)) := by
  intro p q h
  have hp := ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2)
  have hq := ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_right q.1 q.2)
  change ManyBody.Edge.ofAdj _ = ManyBody.Edge.ofAdj _ at h
  rw [h] at hp
  rcases hp with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hq with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact (a1.symm.trans b1)
  · exfalso
    have e1 := a1.symm.trans b1
    have e2 := a2.symm.trans b2
    simp only [Prod.mk.injEq] at e1 e2
    exact zmod_not_add_one_eq_and_add_one_eq _ _ ⟨e1.1, e2.1⟩
  · exfalso
    have e1 := a1.symm.trans b1
    have e2 := a2.symm.trans b2
    simp only [Prod.mk.injEq] at e1 e2
    exact zmod_not_add_one_eq_and_add_one_eq _ _ ⟨e2.1, e1.1⟩
  · exact (a2.symm.trans b2)

/-- On a torus of height at least three, distinct vertices have distinct up edges. -/
theorem torusUpEdge_injective [Fact (2 < height)] :
    Function.Injective (torusUpEdge (width := width) (height := height)) := by
  intro p q h
  have hp := ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2)
  have hq := ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_up q.1 q.2)
  change ManyBody.Edge.ofAdj _ = ManyBody.Edge.ofAdj _ at h
  rw [h] at hp
  rcases hp with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hq with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact (a1.symm.trans b1)
  · exfalso
    have e1 := a1.symm.trans b1
    have e2 := a2.symm.trans b2
    simp only [Prod.mk.injEq] at e1 e2
    exact zmod_not_add_one_eq_and_add_one_eq _ _ ⟨e1.2, e2.2⟩
  · exfalso
    have e1 := a1.symm.trans b1
    have e2 := a2.symm.trans b2
    simp only [Prod.mk.injEq] at e1 e2
    exact zmod_not_add_one_eq_and_add_one_eq _ _ ⟨e2.2, e1.2⟩
  · exact (a2.symm.trans b2)

/-- No right edge is an up edge. -/
theorem torusRightEdge_ne_torusUpEdge (p q : TorusVertex width height) :
    torusRightEdge p ≠ torusUpEdge q := fun h =>
  torusEdge_not_horizontal_and_vertical (torusUpEdge q)
    ⟨h ▸ isHorizontalTorusEdge_torusRightEdge p, isVerticalTorusEdge_torusUpEdge q⟩

end RightAndUpEdges

section ShiftInvariant

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- A function on the torus invariant under the unit horizontal and vertical shifts is
constant. -/
theorem torusVertex_apply_eq_apply_zero_of_shift {α : Type*}
    (f : TorusVertex width height → α)
    (h1 : ∀ v : TorusVertex width height, f (v.1 + 1, v.2) = f v)
    (h2 : ∀ v : TorusVertex width height, f (v.1, v.2 + 1) = f v)
    (v : TorusVertex width height) : f v = f 0 := by
  have hx : ∀ (n : ℕ) (y : ZMod height), f ((n : ZMod width), y) = f (0, y) := by
    intro n y
    induction n with
    | zero => simp
    | succ n ih =>
      calc f (((n + 1 : ℕ) : ZMod width), y) = f ((n : ZMod width) + 1, y) := by
            push_cast; rfl
        _ = f ((n : ZMod width), y) := h1 ((n : ZMod width), y)
        _ = f (0, y) := ih
  have hy : ∀ n : ℕ, f (0, (n : ZMod height)) = f 0 := by
    intro n
    induction n with
    | zero => simp; rfl
    | succ n ih =>
      calc f (0, ((n + 1 : ℕ) : ZMod height)) = f (0, (n : ZMod height) + 1) := by
            push_cast; rfl
        _ = f (0, (n : ZMod height)) := h2 (0, (n : ZMod height))
        _ = f 0 := ih
  obtain ⟨x, y⟩ := v
  rw [← ZMod.natCast_zmod_val x, hx, ← ZMod.natCast_zmod_val y, hy]

end ShiftInvariant

section FourLegs

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-! ### The four legs of a vertex -/

/-- The down leg of `v = (x, y)`: the up edge of `(x, y - 1)`. -/
def torusDownEdge (v : TorusVertex width height) : Edge (torusGraph width height) :=
  torusUpEdge (v.1, v.2 - 1)

/-- The left leg of `v = (x, y)`: the right edge of `(x - 1, y)`. -/
def torusLeftEdge (v : TorusVertex width height) : Edge (torusGraph width height) :=
  torusRightEdge (v.1 - 1, v.2)

/-- The left leg of the right neighbour of `v` is the right edge of `v`. -/
theorem torusLeftEdge_add_one (v : TorusVertex width height) :
    torusLeftEdge (v.1 + 1, v.2) = torusRightEdge v := by
  simp [torusLeftEdge]

/-- The down leg of the upper neighbour of `v` is the up edge of `v`. -/
theorem torusDownEdge_add_one (v : TorusVertex width height) :
    torusDownEdge (v.1, v.2 + 1) = torusUpEdge v := by
  simp [torusDownEdge]

theorem torusRightEdge_incident (v : TorusVertex width height) :
    (torusRightEdge v).1.1 = v ∨ (torusRightEdge v).1.2 = v := by
  rcases ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with ⟨h, _⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem torusUpEdge_incident (v : TorusVertex width height) :
    (torusUpEdge v).1.1 = v ∨ (torusUpEdge v).1.2 = v := by
  rcases ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_up v.1 v.2) with ⟨h, _⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem torusLeftEdge_incident (v : TorusVertex width height) :
    (torusLeftEdge v).1.1 = v ∨ (torusLeftEdge v).1.2 = v := by
  have hv : ((v.1 - 1 + 1, v.2) : TorusVertex width height) = v := by simp
  rcases ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_right (v.1 - 1) v.2) with ⟨_, h⟩ | ⟨h, _⟩
  · exact Or.inr (h.trans hv)
  · exact Or.inl (h.trans hv)

theorem torusDownEdge_incident (v : TorusVertex width height) :
    (torusDownEdge v).1.1 = v ∨ (torusDownEdge v).1.2 = v := by
  have hv : ((v.1, v.2 - 1 + 1) : TorusVertex width height) = v := by simp
  rcases ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_up v.1 (v.2 - 1)) with ⟨_, h⟩ | ⟨h, _⟩
  · exact Or.inr (h.trans hv)
  · exact Or.inl (h.trans hv)

/-- The top leg of `v`, its up edge, as an incident edge. -/
def torusTopLeg (v : TorusVertex width height) : IncidentEdge (torusGraph width height) v :=
  ⟨torusUpEdge v, torusUpEdge_incident v⟩

/-- The right leg of `v`, its right edge, as an incident edge. -/
def torusRightLeg (v : TorusVertex width height) : IncidentEdge (torusGraph width height) v :=
  ⟨torusRightEdge v, torusRightEdge_incident v⟩

/-- The down leg of `v` as an incident edge. -/
def torusDownLeg (v : TorusVertex width height) : IncidentEdge (torusGraph width height) v :=
  ⟨torusDownEdge v, torusDownEdge_incident v⟩

/-- The left leg of `v` as an incident edge. -/
def torusLeftLeg (v : TorusVertex width height) : IncidentEdge (torusGraph width height) v :=
  ⟨torusLeftEdge v, torusLeftEdge_incident v⟩

end FourLegs

section EdgeEquiv

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable [Fact (2 < width)] [Fact (2 < height)]

/-! ### Edges as right edges and up edges -/

/-- On a torus of width and height at least three, the edges are exactly the right edges and
the up edges of the vertices, each counted once. -/
noncomputable def torusEdgeEquiv :
    TorusVertex width height ⊕ TorusVertex width height ≃ Edge (torusGraph width height) :=
  Equiv.ofBijective (Sum.elim torusRightEdge torusUpEdge) <| by
    refine ⟨?_, fun e => ?_⟩
    · rintro (p | p) (q | q) h
      · exact congrArg Sum.inl (torusRightEdge_injective h)
      · exact absurd h (torusRightEdge_ne_torusUpEdge p q)
      · exact absurd h.symm (torusRightEdge_ne_torusUpEdge q p)
      · exact congrArg Sum.inr (torusUpEdge_injective h)
    · rcases torusEdge_horizontal_or_vertical e with he | he
      · obtain ⟨p, rfl⟩ := isHorizontalTorusEdge_eq_rightEdge he
        exact ⟨Sum.inl p, rfl⟩
      · obtain ⟨p, rfl⟩ := isVerticalTorusEdge_eq_upEdge he
        exact ⟨Sum.inr p, rfl⟩

end EdgeEquiv

section IncidentLegs

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The ordered head of a horizontal seam is its native rightward origin. -/
theorem torusRightEdge_head_of_wrap (v : TorusVertex width height) (hv : v.1 + 1 = 0) :
    (torusRightEdge v).1.2 = v := by
  have hv0 : v.1 ≠ 0 := by
    intro h
    simp [h] at hv
  have hcmp : ((v.1 + 1, v.2) : TorusVertex width height) < v := by
    change toLex ((v.1 + 1).val, v.2.val) < toLex (v.1.val, v.2.val)
    rw [Prod.Lex.toLex_lt_toLex, hv, ZMod.val_zero]
    exact Or.inl (ZMod.val_pos.mpr hv0)
  rw [torusRightEdge, ManyBody.Edge.ofAdj_of_gt (torusGraph_adj_right v.1 v.2) hcmp]

/-- The ordered head of a vertical seam is its native upward origin. -/
theorem torusUpEdge_head_of_wrap (v : TorusVertex width height) (hv : v.2 + 1 = 0) :
    (torusUpEdge v).1.2 = v := by
  have hv0 : v.2 ≠ 0 := by
    intro h
    simp [h] at hv
  have hcmp : ((v.1, v.2 + 1) : TorusVertex width height) < v := by
    change toLex (v.1.val, (v.2 + 1).val) < toLex (v.1.val, v.2.val)
    rw [Prod.Lex.toLex_lt_toLex, hv, ZMod.val_zero]
    exact Or.inr ⟨rfl, ZMod.val_pos.mpr hv0⟩
  rw [torusUpEdge, ManyBody.Edge.ofAdj_of_gt (torusGraph_adj_up v.1 v.2) hcmp]

private theorem torusIncidentEdge_eq_leg (v : TorusVertex width height)
    (f : IncidentEdge (torusGraph width height) v) :
    f = torusTopLeg v ∨ f = torusRightLeg v ∨ f = torusDownLeg v ∨ f = torusLeftLeg v := by
  obtain ⟨z, hz⟩ := torusEdgeEquiv.surjective f.1
  rcases z with p | p
  · change torusRightEdge p = f.1 at hz
    have hi := f.2
    rw [← hz] at hi
    have hep := ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2)
    have hp : p = v ∨ (p.1 + 1, p.2) = v := by
      rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi with hi | hi
      · exact Or.inl (h1.symm.trans hi)
      · exact Or.inr (h2.symm.trans hi)
      · exact Or.inr (h1.symm.trans hi)
      · exact Or.inl (h2.symm.trans hi)
    rcases hp with rfl | hp
    · exact Or.inr (Or.inl (Subtype.ext hz.symm))
    · have hp' : p = (v.1 - 1, v.2) := by
        have hx := congrArg Prod.fst hp
        have hy := congrArg Prod.snd hp
        exact Prod.ext ((eq_sub_iff_add_eq).mpr hx) hy
      exact Or.inr (Or.inr (Or.inr (Subtype.ext (by rw [← hz, hp']; rfl))))
  · change torusUpEdge p = f.1 at hz
    have hi := f.2
    rw [← hz] at hi
    have hep := ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2)
    have hp : p = v ∨ (p.1, p.2 + 1) = v := by
      rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi with hi | hi
      · exact Or.inl (h1.symm.trans hi)
      · exact Or.inr (h2.symm.trans hi)
      · exact Or.inr (h1.symm.trans hi)
      · exact Or.inl (h2.symm.trans hi)
    rcases hp with rfl | hp
    · exact Or.inl (Subtype.ext hz.symm)
    · have hp' : p = (v.1, v.2 - 1) := by
        have hx := congrArg Prod.fst hp
        have hy := congrArg Prod.snd hp
        exact Prod.ext hx ((eq_sub_iff_add_eq).mpr hy)
      exact Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [← hz, hp']; rfl))))

/-- The four native legs enumerate the incident edges of a vertex.
Source: SCP10, square-lattice virtual legs in Definition 6.1. -/
def torusIncidentLeg (v : TorusVertex width height) :
    Fin 4 → IncidentEdge (torusGraph width height) v :=
  ![torusTopLeg v, torusRightLeg v, torusDownLeg v, torusLeftLeg v]

/-- No incident torus edge is omitted by the four native legs.
Source: SCP10, square-lattice construction at lines 1935–1990. -/
theorem torusIncidentLeg_surjective (v : TorusVertex width height) :
    Function.Surjective (torusIncidentLeg v) := by
  intro f
  rcases torusIncidentEdge_eq_leg v f with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The four native virtual legs are distinct when both periods are at least
three. Source: SCP10, square-lattice construction at lines 1935–1990. -/
theorem torusIncidentLeg_injective (v : TorusVertex width height) :
    Function.Injective (torusIncidentLeg v) := by
  have htr : torusTopLeg v ≠ torusRightLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge v v (congrArg Subtype.val h).symm
  have htl : torusTopLeg v ≠ torusLeftLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge (v.1 - 1, v.2) v (congrArg Subtype.val h).symm
  have hrd : torusRightLeg v ≠ torusDownLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge v (v.1, v.2 - 1) (congrArg Subtype.val h)
  have hdl : torusDownLeg v ≠ torusLeftLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge (v.1 - 1, v.2) (v.1, v.2 - 1)
      (congrArg Subtype.val h).symm
  have htd : torusTopLeg v ≠ torusDownLeg v := by
    intro h
    have hy := congrArg Prod.snd (torusUpEdge_injective (congrArg Subtype.val h))
    exact one_ne_zero (α := ZMod height)
      (add_left_cancel (by simpa only [add_zero] using eq_sub_iff_add_eq.mp hy))
  have hrl : torusRightLeg v ≠ torusLeftLeg v := by
    intro h
    have hx := congrArg Prod.fst (torusRightEdge_injective (congrArg Subtype.val h))
    exact one_ne_zero (α := ZMod width)
      (add_left_cancel (by simpa only [add_zero] using eq_sub_iff_add_eq.mp hx))
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [torusIncidentLeg]

/-- Numbering the four actual incident bonds in top, right, down, left order.
Source: SCP10, square-lattice virtual legs in Definition 6.1. -/
noncomputable def torusIncidentLegEquiv (v : TorusVertex width height) :
    Fin 4 ≃ IncidentEdge (torusGraph width height) v :=
  Equiv.ofBijective (torusIncidentLeg v)
    ⟨torusIncidentLeg_injective v, torusIncidentLeg_surjective v⟩

end IncidentLegs

end PEPS
end TNLean
