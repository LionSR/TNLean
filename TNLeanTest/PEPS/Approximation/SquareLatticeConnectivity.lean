/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareLatticeConnectivity

/-!
# Regression checks for rectangular square-lattice connectivity

Zero dimensions remain preconnected but are not connected. Positive
rectangles include the singleton lattice. The nontrivial-square theorem
provides the local instance needed to obtain an incident edge at every site.
-/

namespace TNLean.PEPS

example : (squareLatticeGraph 0 3).Preconnected :=
  squareLatticeGraph_preconnected 0 3

example : ¬ (squareLatticeGraph 0 3).Connected := by
  simp only [squareLatticeGraph_connected_iff, Nat.lt_irrefl, false_and, not_false_eq_true]

example : ¬ (squareLatticeGraph 3 0).Connected := by
  simp only [squareLatticeGraph_connected_iff, Nat.lt_irrefl, and_false, not_false_eq_true]

example : (squareLatticeGraph 1 1).Connected :=
  squareLatticeGraph_connected (by decide) (by decide)

example : (squareLatticeGraph 2 3).Connected :=
  squareLatticeGraph_connected (by decide) (by decide)

example {width height : ℕ} (hwidth : 0 < width) (hheight : 0 < height)
    (u v : SquareLatticeVertex width height) :
    (squareLatticeGraph width height).Reachable u v :=
  squareLatticeGraph_connected hwidth hheight u v

example {L : ℕ} (hL : 2 ≤ L) (v : SquareLatticeVertex L L) :
    ∃ w, (squareLatticeGraph L L).Adj v w := by
  let := squareLatticeVertex_nontrivial hL
  have hpos : 0 < L := by omega
  exact (squareLatticeGraph_connected hpos hpos).preconnected.exists_adj_of_nontrivial v

end TNLean.PEPS
