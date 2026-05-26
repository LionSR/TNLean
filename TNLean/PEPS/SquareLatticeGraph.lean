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
  symm := by
    intro v w h
    rcases h with h | h
    · rcases h with ⟨hy, hx | hx⟩
      · exact Or.inl ⟨hy.symm, Or.inr hx⟩
      · exact Or.inl ⟨hy.symm, Or.inl hx⟩
    · rcases h with ⟨hx, hy | hy⟩
      · exact Or.inr ⟨hx.symm, Or.inr hy⟩
      · exact Or.inr ⟨hx.symm, Or.inl hy⟩
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

end PEPS
end TNLean
