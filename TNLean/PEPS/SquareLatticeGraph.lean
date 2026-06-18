import Mathlib.Data.Prod.Lex

import TNLean.PEPS.NormalBlocking

/-!
# Square-lattice graph for the normal PEPS proof

This file records the nearest-neighbor graph on the finite rectangular
coordinate lattice used in the normal PEPS proof.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3]
-/

namespace TNLean
namespace PEPS

/-- The coordinate vertex set is ordered lexicographically.  The project-level
`Edge` type uses an ambient linear order to orient undirected graph edges, so
this instance lets the square-lattice graph use the same edge type as the
general PEPS development.

The decidable-equality field is pinned to the canonical product decidable
equality `instDecidableEqProd` rather than the comparison-derived one that
`LinearOrder.lift'` would synthesize.  The square-lattice geometry layer builds
its blocking data over the product decidable equality, while the per-edge gauge
interface synthesizes a decidable equality from this linear order; pinning the
field makes the two definitionally equal, so an interior blocking datum feeds the
gauge interface with no subsingleton transport.  All other order fields are taken
from `LinearOrder.lift'`, so the lexicographic comparison is unchanged. -/
instance instLinearOrderSquareLatticeVertex (width height : ℕ) :
    LinearOrder (SquareLatticeVertex width height) :=
  let src : LinearOrder (SquareLatticeVertex width height) :=
    LinearOrder.lift' (fun v : SquareLatticeVertex width height => toLex v) (by
      intro v w h
      simpa using congrArg ofLex h)
  @Function.Injective.linearOrder _ _ _ src.toLE src.toLT src.toMax src.toMin src.toOrd
    instDecidableEqProd src.toDecidableLE src.toDecidableLT
    (fun v : SquareLatticeVertex width height => toLex v)
    (fun v w h => by simpa using congrArg ofLex h)
    (le := Iff.rfl) (lt := Iff.rfl)
    (min := fun _ _ => rfl) (max := fun _ _ => rfl)
    (compare := fun _ _ => rfl)

/-- Horizontal nearest-neighbor relation in a finite rectangular square
lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`, where the edge blocking is applied to
horizontal and vertical lattice edges. -/
def squareLatticeHorizontalNeighbor {width height : ℕ}
    (v w : SquareLatticeVertex width height) : Prop :=
  v.2 = w.2 ∧ (v.1.1 + 1 = w.1.1 ∨ w.1.1 + 1 = v.1.1)

/-- Vertical nearest-neighbor relation in a finite rectangular square lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`, where the edge blocking is applied to
horizontal and vertical lattice edges. -/
def squareLatticeVerticalNeighbor {width height : ℕ}
    (v w : SquareLatticeVertex width height) : Prop :=
  v.1 = w.1 ∧ (v.2.1 + 1 = w.2.1 ∨ w.2.1 + 1 = v.2.1)

/-- The finite rectangular square-lattice graph with nearest-neighbor
horizontal and vertical edges.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`, where a \(7\times7\) square lattice is
blocked around every horizontal and vertical edge. -/
def squareLatticeGraph (width height : ℕ) : SimpleGraph (SquareLatticeVertex width height) where
  Adj v w := squareLatticeHorizontalNeighbor v w ∨ squareLatticeVerticalNeighbor v w
  symm := ⟨by
    intro v w h
    rcases h with h | h
    · rcases h with ⟨hy, hx | hx⟩
      · exact Or.inl ⟨hy.symm, Or.inr hx⟩
      · exact Or.inl ⟨hy.symm, Or.inl hx⟩
    · rcases h with ⟨hx, hy | hy⟩
      · exact Or.inr ⟨hx.symm, Or.inr hy⟩
      · exact Or.inr ⟨hx.symm, Or.inl hy⟩⟩
  loopless := by
    constructor
    intro v h
    rcases h with h | h
    · rcases h with ⟨_, h | h⟩ <;> omega
    · rcases h with ⟨_, h | h⟩ <;> omega

instance instDecidableRelSquareLatticeGraphAdj (width height : ℕ) :
    DecidableRel (squareLatticeGraph width height).Adj := by
  unfold squareLatticeGraph squareLatticeHorizontalNeighbor squareLatticeVerticalNeighbor
  infer_instance

@[simp] theorem squareLatticeGraph_adj {width height : ℕ}
    (v w : SquareLatticeVertex width height) :
    (squareLatticeGraph width height).Adj v w ↔
      squareLatticeHorizontalNeighbor v w ∨ squareLatticeVerticalNeighbor v w :=
  Iff.rfl

/-- A vertex and its right neighbor are adjacent in the square-lattice graph.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem squareLatticeGraph_adj_right {width height : ℕ}
    (x : Fin width) (y : Fin height) (hx : x.1 + 1 < width) :
    (squareLatticeGraph width height).Adj (x, y) (⟨x.1 + 1, hx⟩, y) := by
  exact Or.inl ⟨rfl, Or.inl rfl⟩

/-- A vertex and its upper neighbor are adjacent in the square-lattice graph.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem squareLatticeGraph_adj_up {width height : ℕ}
    (x : Fin width) (y : Fin height) (hy : y.1 + 1 < height) :
    (squareLatticeGraph width height).Adj (x, y) (x, ⟨y.1 + 1, hy⟩) := by
  exact Or.inr ⟨rfl, Or.inl rfl⟩

/-- The horizontal edge from coordinate \((x,y)\) to \((x+1,y)\).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where translated horizontal edge blockings are placed around lattice edges. -/
def squareLatticeRightEdge {width height : ℕ} (x y : ℕ)
    (hx : x + 1 < width) (hy : y < height) :
    Edge (squareLatticeGraph width height) where
  val :=
    (((⟨x, by omega⟩ : Fin width), (⟨y, hy⟩ : Fin height)),
      ((⟨x + 1, hx⟩ : Fin width), (⟨y, hy⟩ : Fin height)))
  property := by
    constructor
    · change toLex
        (((⟨x, by omega⟩ : Fin width), (⟨y, hy⟩ : Fin height)) :
            SquareLatticeVertex width height) <
        toLex (((⟨x + 1, hx⟩ : Fin width), (⟨y, hy⟩ : Fin height)) :
            SquareLatticeVertex width height)
      rw [Prod.Lex.toLex_lt_toLex]
      simp
    · exact squareLatticeGraph_adj_right ⟨x, by omega⟩ ⟨y, hy⟩ hx

/-- The vertical edge from coordinate \((x,y)\) to \((x,y+1)\).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where translated vertical edge blockings are placed around lattice edges. -/
def squareLatticeUpEdge {width height : ℕ} (x y : ℕ)
    (hx : x < width) (hy : y + 1 < height) :
    Edge (squareLatticeGraph width height) where
  val :=
    (((⟨x, hx⟩ : Fin width), (⟨y, by omega⟩ : Fin height)),
      ((⟨x, hx⟩ : Fin width), (⟨y + 1, hy⟩ : Fin height)))
  property := by
    constructor
    · change toLex
        (((⟨x, hx⟩ : Fin width), (⟨y, by omega⟩ : Fin height)) :
            SquareLatticeVertex width height) <
        toLex (((⟨x, hx⟩ : Fin width), (⟨y + 1, hy⟩ : Fin height)) :
            SquareLatticeVertex width height)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨rfl, by simp⟩
    · exact squareLatticeGraph_adj_up ⟨x, hx⟩ ⟨y, by omega⟩ hy

/-- An edge of the finite square-lattice graph is horizontal when its endpoints
are horizontal nearest neighbors.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where horizontal and vertical edge blockings are treated separately. -/
def IsHorizontalSquareLatticeEdge {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) : Prop :=
  squareLatticeHorizontalNeighbor e.1.1 e.1.2

/-- An edge of the finite square-lattice graph is vertical when its endpoints
are vertical nearest neighbors.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where horizontal and vertical edge blockings are treated separately. -/
def IsVerticalSquareLatticeEdge {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) : Prop :=
  squareLatticeVerticalNeighbor e.1.1 e.1.2

/-- A coordinate right edge is horizontal.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem squareLatticeRightEdge_isHorizontal {width height : ℕ} {x y : ℕ}
    (hx : x + 1 < width) (hy : y < height) :
    IsHorizontalSquareLatticeEdge (squareLatticeRightEdge x y hx hy) := by
  change squareLatticeHorizontalNeighbor
    (squareLatticeRightEdge x y hx hy).1.1
    (squareLatticeRightEdge x y hx hy).1.2
  simp [squareLatticeRightEdge, squareLatticeHorizontalNeighbor]

/-- A coordinate upward edge is vertical.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem squareLatticeUpEdge_isVertical {width height : ℕ} {x y : ℕ}
    (hx : x < width) (hy : y + 1 < height) :
    IsVerticalSquareLatticeEdge (squareLatticeUpEdge x y hx hy) := by
  change squareLatticeVerticalNeighbor
    (squareLatticeUpEdge x y hx hy).1.1
    (squareLatticeUpEdge x y hx hy).1.2
  simp [squareLatticeUpEdge, squareLatticeVerticalNeighbor]

/-- Every edge of the finite square-lattice graph is horizontal or vertical.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem squareLatticeEdge_horizontal_or_vertical {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) :
    IsHorizontalSquareLatticeEdge e ∨ IsVerticalSquareLatticeEdge e := by
  exact e.2.2

/-- No edge of the finite square-lattice graph is both horizontal and vertical.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem squareLatticeEdge_not_horizontal_and_vertical {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) :
    ¬ (IsHorizontalSquareLatticeEdge e ∧ IsVerticalSquareLatticeEdge e) := by
  rintro ⟨hHorizontal, hVertical⟩
  have hx :
      e.1.1.1.1 = e.1.2.1.1 := by
    exact congrArg Fin.val hVertical.1
  rcases hHorizontal.2 with hStep | hStep <;> omega

/-- The ordered endpoints of a horizontal square-lattice edge go from left to
right.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the normalized horizontal edge blocking is translated to horizontal
lattice edges. -/
theorem horizontalSquareLatticeEdge_coords {width height : ℕ}
    (e : Edge (squareLatticeGraph width height))
    (h : IsHorizontalSquareLatticeEdge e) :
    e.1.1.2 = e.1.2.2 ∧ e.1.1.1.1 + 1 = e.1.2.1.1 := by
  rcases h with ⟨hy, hstep | hstep⟩
  · exact ⟨hy, hstep⟩
  · exfalso
    have hlt := e.2.1
    change toLex e.1.1 < toLex e.1.2 at hlt
    rw [Prod.Lex.toLex_lt_toLex] at hlt
    rcases hlt with hx | hxy
    · omega
    · rcases hxy with ⟨_hxEq, hylt⟩
      rw [hy] at hylt
      exact (lt_irrefl e.1.2.2 hylt).elim

/-- A horizontal square-lattice edge is the coordinate right edge from its
ordered left endpoint.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem horizontalSquareLatticeEdge_eq_rightEdge {width height : ℕ}
    (e : Edge (squareLatticeGraph width height))
    (h : IsHorizontalSquareLatticeEdge e) :
    e = squareLatticeRightEdge e.1.1.1.1 e.1.1.2.1 (by
      have hc := horizontalSquareLatticeEdge_coords e h
      have _hright := e.1.2.1.2
      omega) e.1.1.2.2 := by
  have hc := horizontalSquareLatticeEdge_coords e h
  ext <;> simp only [squareLatticeRightEdge]
  · exact hc.2.symm
  · exact congrArg Fin.val hc.1.symm

/-- The ordered endpoints of a vertical square-lattice edge go from bottom to
top.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the normalized vertical edge blocking is translated to vertical lattice
edges. -/
theorem verticalSquareLatticeEdge_coords {width height : ℕ}
    (e : Edge (squareLatticeGraph width height))
    (h : IsVerticalSquareLatticeEdge e) :
    e.1.1.1 = e.1.2.1 ∧ e.1.1.2.1 + 1 = e.1.2.2.1 := by
  rcases h with ⟨hx, hstep | hstep⟩
  · exact ⟨hx, hstep⟩
  · exfalso
    have hlt := e.2.1
    change toLex e.1.1 < toLex e.1.2 at hlt
    rw [Prod.Lex.toLex_lt_toLex] at hlt
    rcases hlt with hxlt | hxy
    · rw [hx] at hxlt
      exact (lt_irrefl e.1.2.1 hxlt).elim
    · rcases hxy with ⟨_hxEq, _hylt⟩
      omega

/-- A vertical square-lattice edge is the coordinate upward edge from its
ordered lower endpoint.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem verticalSquareLatticeEdge_eq_upEdge {width height : ℕ}
    (e : Edge (squareLatticeGraph width height))
    (h : IsVerticalSquareLatticeEdge e) :
    e = squareLatticeUpEdge e.1.1.1.1 e.1.1.2.1 e.1.1.1.2 (by
      have hc := verticalSquareLatticeEdge_coords e h
      have _htop := e.1.2.2.2
      omega) := by
  have hc := verticalSquareLatticeEdge_coords e h
  ext <;> simp only [squareLatticeUpEdge]
  · exact congrArg Fin.val hc.1.symm
  · exact hc.2.symm

end PEPS
end TNLean
