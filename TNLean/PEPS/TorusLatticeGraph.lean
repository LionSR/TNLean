import Mathlib.Data.Prod.Lex
import Mathlib.Data.ZMod.Basic

import TNLean.PEPS.Defs

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

The open rectangular model `TNLean/PEPS/SquareLatticeGraph.lean` has a boundary
that breaks translation: its boundary edges have no interior margin, so the
every-edge blocking construction only reaches interior edges
(`docs/paper-gaps/peps_normal_ft_section3_route.tex`, remaining obligation 4).
The torus removes the boundary, so on it every edge is interior and the
construction is complete (same note, remaining obligation 6). This file records
the torus geometry natively; the bridge transferring the merged interior-edge
blocking machinery from the open lattice onto the torus is a separate step.

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
(`TNLean.PEPS.instLinearOrderSquareLatticeVertex`). As there, the
`toDecidableEq` field is pinned to the canonical product decidable equality
`instDecidableEqProd` rather than the comparison-derived one that
`LinearOrder.lift'` would synthesize, so the geometry layer (which builds its
data over the product decidable equality) and the gauge interface (which
synthesizes a decidable equality from the linear order) meet definitionally.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

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
`TNLean.PEPS.instLinearOrderSquareLatticeVertex`.  All other order fields are
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
        show (fun v : TorusVertex width height => toLex (v.1.val, v.2.val)) (src.min x y) = _
        rw [src.min_def]; split
        · rw [min_eq_left ‹_›]
        · rw [min_eq_right (not_le.mp ‹_›).le])
      (max := fun x y => by
        show (fun v : TorusVertex width height => toLex (v.1.val, v.2.val)) (src.max x y) = _
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
  symm := by
    intro v w h
    rcases h with ⟨hy, hx | hx⟩ | ⟨hx, hy | hy⟩
    · exact Or.inl ⟨hy.symm, Or.inr hx⟩
    · exact Or.inl ⟨hy.symm, Or.inl hx⟩
    · exact Or.inr ⟨hx.symm, Or.inr hy⟩
    · exact Or.inr ⟨hx.symm, Or.inl hy⟩
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

end PEPS
end TNLean
