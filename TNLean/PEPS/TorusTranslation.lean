import Mathlib.Combinatorics.SimpleGraph.Maps

import TNLean.PEPS.TorusLatticeGraph

/-!
# Translation automorphisms of the periodic (torus) lattice

The translationally invariant normal PEPS theorem (arXiv:1804.04964, Section 3,
proof of Theorem 3) places one tensor at every site of a lattice on which
translation is a symmetry. On the discrete torus
(`TNLean/PEPS/TorusLatticeGraph.lean`) translation by a coordinate offset
`(a, b)` is the vertex map `(x, y) ↦ (x + a, y + b)`, with addition taken
cyclically in each coordinate ring. This map is a bijection (`translateEquiv`)
that preserves the cyclic nearest-neighbour adjacency, hence a graph
automorphism (`translate`). It carries each edge to an edge of the same
orientation, and the induced action on edges (`translateEdge`) reorders the
translated endpoints back into the `Edge` convention through `Edge.ofAdj`,
because a translation can swap the lexicographic order of the two endpoints when
the coordinate wraps around the torus.

These automorphisms are the symmetry under which a translation-invariant tensor
is fixed (`TNLean/PEPS/TorusTranslationInvariant.lean`); their edge action is the
input to that invariance and to the covariance of the blocked machinery.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-! ### The translation bijection -/

/-- Translation of torus coordinates by the offset `(a, b)`: the bijection
`(x, y) ↦ (x + a, y + b)`, with cyclic addition in each coordinate ring.  Its
inverse subtracts the offset.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the translationally invariant theorem
repeats one tensor at every site. -/
def translateEquiv (a : ZMod width) (b : ZMod height) :
    TorusVertex width height ≃ TorusVertex width height where
  toFun v := (v.1 + a, v.2 + b)
  invFun v := (v.1 - a, v.2 - b)
  left_inv v := by simp
  right_inv v := by simp

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
@[simp] theorem translateEquiv_apply (a : ZMod width) (b : ZMod height)
    (v : TorusVertex width height) :
    translateEquiv a b v = (v.1 + a, v.2 + b) :=
  rfl

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
@[simp] theorem translateEquiv_symm_apply (a : ZMod width) (b : ZMod height)
    (v : TorusVertex width height) :
    (translateEquiv a b).symm v = (v.1 - a, v.2 - b) :=
  rfl

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
/-- The translation bijection preserves the horizontal cyclic-neighbour relation:
adding the same offset to both endpoints preserves a horizontal step. -/
theorem torusHorizontalNeighbor_translate (a : ZMod width) (b : ZMod height)
    {v w : TorusVertex width height} :
    torusHorizontalNeighbor (translateEquiv a b v) (translateEquiv a b w) ↔
      torusHorizontalNeighbor v w := by
  simp only [torusHorizontalNeighbor, translateEquiv_apply]
  constructor
  · rintro ⟨hy, hx | hx⟩
    · exact ⟨add_right_cancel hy, Or.inl (add_right_cancel (by rw [add_right_comm]; exact hx))⟩
    · exact ⟨add_right_cancel hy, Or.inr (add_right_cancel (by rw [add_right_comm]; exact hx))⟩
  · rintro ⟨hy, hx | hx⟩
    · exact ⟨by rw [hy], Or.inl (by rw [add_right_comm, hx])⟩
    · exact ⟨by rw [hy], Or.inr (by rw [add_right_comm, hx])⟩

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
/-- The translation bijection preserves the vertical cyclic-neighbour relation. -/
theorem torusVerticalNeighbor_translate (a : ZMod width) (b : ZMod height)
    {v w : TorusVertex width height} :
    torusVerticalNeighbor (translateEquiv a b v) (translateEquiv a b w) ↔
      torusVerticalNeighbor v w := by
  simp only [torusVerticalNeighbor, translateEquiv_apply]
  constructor
  · rintro ⟨hx, hy | hy⟩
    · exact ⟨add_right_cancel hx, Or.inl (add_right_cancel (by rw [add_right_comm]; exact hy))⟩
    · exact ⟨add_right_cancel hx, Or.inr (add_right_cancel (by rw [add_right_comm]; exact hy))⟩
  · rintro ⟨hx, hy | hy⟩
    · exact ⟨by rw [hx], Or.inl (by rw [add_right_comm, hy])⟩
    · exact ⟨by rw [hx], Or.inr (by rw [add_right_comm, hy])⟩

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
/-- The horizontal cyclic-neighbour relation is symmetric. -/
theorem torusHorizontalNeighbor_symm {v w : TorusVertex width height}
    (h : torusHorizontalNeighbor v w) : torusHorizontalNeighbor w v :=
  ⟨h.1.symm, h.2.imp (·) (·) |>.elim Or.inr Or.inl⟩

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
/-- The vertical cyclic-neighbour relation is symmetric. -/
theorem torusVerticalNeighbor_symm {v w : TorusVertex width height}
    (h : torusVerticalNeighbor v w) : torusVerticalNeighbor w v :=
  ⟨h.1.symm, h.2.imp (·) (·) |>.elim Or.inr Or.inl⟩

/-! ### The translation graph automorphism -/

/-- Translation of the torus by `(a, b)` as a graph automorphism: the coordinate
bijection `translateEquiv a b` together with adjacency preservation in both
directions.  Translation carries horizontal edges to horizontal edges and
vertical edges to vertical edges, so it preserves the union adjacency.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
def translate (a : ZMod width) (b : ZMod height) :
    torusGraph width height ≃g torusGraph width height :=
  { toEquiv := translateEquiv a b
    map_rel_iff' := by
      intro v w
      change torusHorizontalNeighbor (translateEquiv a b v) (translateEquiv a b w) ∨
          torusVerticalNeighbor (translateEquiv a b v) (translateEquiv a b w) ↔
        torusHorizontalNeighbor v w ∨ torusVerticalNeighbor v w
      rw [torusHorizontalNeighbor_translate, torusVerticalNeighbor_translate] }

@[simp] theorem translate_apply (a : ZMod width) (b : ZMod height)
    (v : TorusVertex width height) :
    translate a b v = (v.1 + a, v.2 + b) :=
  rfl

/-- Translation preserves adjacency in the forward direction. -/
theorem torusGraph_adj_translate (a : ZMod width) (b : ZMod height)
    {v w : TorusVertex width height} (h : (torusGraph width height).Adj v w) :
    (torusGraph width height).Adj (translate a b v) (translate a b w) :=
  (translate a b).map_rel_iff'.mpr h

/-! ### The induced action on edges

An edge of the torus is an ordered pair `(u, v)` with `u < v`.  Translation may
swap the lexicographic order of the two translated endpoints (the coordinate
value wraps around the torus), so the edge action applies the translation to both
endpoints and reorders the result back into the `Edge` convention through
`Edge.ofAdj`. -/

/-- The action of the translation `(a, b)` on a torus edge: apply the translation
to both endpoints and reorder them into the `Edge` convention.  The orientation
bookkeeping is explicit — the unordered endpoint pair is the translate of the
original, and `Edge.ofAdj` puts the smaller endpoint first, which a wraparound
translate may have flipped.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def translateEdge (a : ZMod width) (b : ZMod height)
    (e : Edge (torusGraph width height)) : Edge (torusGraph width height) :=
  Edge.ofAdj (torusGraph_adj_translate a b e.2.2)

/-- The unordered endpoints of `translateEdge a b e` are the translates of the
endpoints of `e`. -/
theorem translateEdge_endpoints (a : ZMod width) (b : ZMod height)
    (e : Edge (torusGraph width height)) :
    ((translateEdge a b e).1.1 = translate a b e.1.1 ∧
        (translateEdge a b e).1.2 = translate a b e.1.2) ∨
      ((translateEdge a b e).1.1 = translate a b e.1.2 ∧
        (translateEdge a b e).1.2 = translate a b e.1.1) :=
  Edge.ofAdj_endpoints (torusGraph_adj_translate a b e.2.2)

/-- The translation edge action preserves horizontal orientation: the translate of
a horizontal edge is horizontal. -/
theorem translateEdge_isHorizontal (a : ZMod width) (b : ZMod height)
    {e : Edge (torusGraph width height)} (he : IsHorizontalTorusEdge e) :
    IsHorizontalTorusEdge (translateEdge a b e) := by
  have hadj : torusHorizontalNeighbor (translate a b e.1.1) (translate a b e.1.2) :=
    (torusHorizontalNeighbor_translate a b).mpr he
  rcases translateEdge_endpoints a b e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · change torusHorizontalNeighbor _ _; rw [h1, h2]; exact hadj
  · change torusHorizontalNeighbor _ _; rw [h1, h2]; exact torusHorizontalNeighbor_symm hadj

/-- The translation edge action preserves vertical orientation: the translate of a
vertical edge is vertical. -/
theorem translateEdge_isVertical (a : ZMod width) (b : ZMod height)
    {e : Edge (torusGraph width height)} (he : IsVerticalTorusEdge e) :
    IsVerticalTorusEdge (translateEdge a b e) := by
  have hadj : torusVerticalNeighbor (translate a b e.1.1) (translate a b e.1.2) :=
    (torusVerticalNeighbor_translate a b).mpr he
  rcases translateEdge_endpoints a b e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · change torusVerticalNeighbor _ _; rw [h1, h2]; exact hadj
  · change torusVerticalNeighbor _ _; rw [h1, h2]; exact torusVerticalNeighbor_symm hadj

/-! ### The induced action on incident edges

An edge incident to `v` is incident, after translation, to `translate a b v`: the
translated edge keeps the same incidence because translation carries the endpoint
`v` to `translate a b v`. -/

/-- The translation action on edges incident to a vertex `v`, landing in the edges
incident to `translate a b v`.  The underlying edge is `translateEdge a b`; the
incidence is preserved because translation sends the endpoint equal to `v` to one
equal to `translate a b v`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def translateIncidentEdge (a : ZMod width) (b : ZMod height) (v : TorusVertex width height)
    (ie : IncidentEdge (torusGraph width height) v) :
    IncidentEdge (torusGraph width height) (translate a b v) :=
  ⟨translateEdge a b ie.1, by
    rcases translateEdge_endpoints a b ie.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases ie.2 with hv | hv
      · exact Or.inl (by rw [h1, hv])
      · exact Or.inr (by rw [h2, hv])
    · rcases ie.2 with hv | hv
      · exact Or.inr (by rw [h2, hv])
      · exact Or.inl (by rw [h1, hv])⟩

@[simp] theorem translateIncidentEdge_coe (a : ZMod width) (b : ZMod height)
    (v : TorusVertex width height) (ie : IncidentEdge (torusGraph width height) v) :
    (translateIncidentEdge a b v ie).1 = translateEdge a b ie.1 :=
  rfl

end PEPS
end TNLean
