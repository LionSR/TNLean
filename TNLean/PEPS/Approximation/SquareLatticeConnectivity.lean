/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Hasse

import TNLean.PEPS.SquareLatticeGraph

/-!
# Connectivity of finite rectangular square lattices

The nearest-neighbor square-lattice graph is the box product of two finite
path graphs. It is preconnected for all dimensions and connected exactly when
both dimensions are positive. A square with side length at least two has a
nontrivial vertex type.

These are geometric facts about the rectangular lattice used in
arXiv:1804.04964, Section 3, Theorem 3. They also supply the connectivity
hypotheses for exact finite-graph PEPS constructions.
-/

namespace TNLean.PEPS

/-- A rectangular nearest-neighbor lattice is the box product of its two
coordinate path graphs. -/
theorem squareLatticeGraph_eq_boxProd (width height : ℕ) :
    squareLatticeGraph width height =
      SimpleGraph.boxProd (SimpleGraph.pathGraph width) (SimpleGraph.pathGraph height) := by
  ext v w
  simp only [squareLatticeGraph_adj, squareLatticeHorizontalNeighbor,
    squareLatticeVerticalNeighbor, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj,
    and_comm]

/-- Every two vertices of a finite rectangular square lattice are joined by
a walk, including the vacuous cases with a zero dimension. -/
theorem squareLatticeGraph_preconnected (width height : ℕ) :
    (squareLatticeGraph width height).Preconnected := by
  rw [squareLatticeGraph_eq_boxProd]
  exact (SimpleGraph.pathGraph_preconnected width).boxProd
    (SimpleGraph.pathGraph_preconnected height)

/-- A finite rectangular square lattice with positive dimensions is connected. -/
theorem squareLatticeGraph_connected {width height : ℕ}
    (hwidth : 0 < width) (hheight : 0 < height) :
    (squareLatticeGraph width height).Connected where
  preconnected := squareLatticeGraph_preconnected width height
  nonempty := ⟨(⟨0, hwidth⟩, ⟨0, hheight⟩)⟩

/-- Connectivity of a rectangular square lattice is equivalent to positivity
of both side lengths. -/
theorem squareLatticeGraph_connected_iff (width height : ℕ) :
    (squareLatticeGraph width height).Connected ↔ 0 < width ∧ 0 < height := by
  constructor
  · intro h
    obtain ⟨v⟩ := h.nonempty
    exact ⟨Nat.zero_lt_of_lt v.1.isLt, Nat.zero_lt_of_lt v.2.isLt⟩
  · rintro ⟨hwidth, hheight⟩
    exact squareLatticeGraph_connected hwidth hheight

/-- A square lattice of side length at least two has distinct vertices.
This theorem can be installed locally as a typeclass instance. -/
theorem squareLatticeVertex_nontrivial {L : ℕ} (hL : 2 ≤ L) :
    Nontrivial (SquareLatticeVertex L L) := by
  let : Nontrivial (Fin L) := Fin.nontrivial_iff_two_le.mpr hL
  infer_instance

end TNLean.PEPS
