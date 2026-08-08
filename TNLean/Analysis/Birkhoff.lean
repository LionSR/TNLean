/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Birkhoff's theorem for doubly stochastic matrices (Wolf Chapter 8)

The doubly-stochastic half of Birkhoff's theorem: the set of `d × d`
doubly stochastic matrices over `ℝ` is the convex hull of the `d × d`
permutation matrices, and its extreme points are exactly the
permutation matrices.

Source: `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 263–266.
-/

open Set

namespace TNLean

/--
**Birkhoff's theorem** (doubly-stochastic half, Wolf Chapter 8, lines 263–266).

The set of `d × d` doubly stochastic matrices over `ℝ` equals the convex
hull of the `d × d` permutation matrices.
-/
theorem wolf_birkhoff_doubly_stochastic_convex_hull {d : ℕ} :
    (doublyStochastic ℝ (Fin d) : Set (Matrix (Fin d) (Fin d) ℝ)) =
      convexHull ℝ {σ.permMatrix ℝ | σ : Equiv.Perm (Fin d)} :=
  _root_.doublyStochastic_eq_convexHull_permMatrix

/--
**Birkhoff's theorem** (doubly-stochastic half, Wolf Chapter 8, lines 263–266).

The extreme points of the set of `d × d` doubly stochastic matrices over
`ℝ` are exactly the `d × d` permutation matrices.
-/
theorem wolf_birkhoff_extreme_points_doubly_stochastic {d : ℕ} :
    Set.extremePoints ℝ ((doublyStochastic ℝ (Fin d) : Set (Matrix (Fin d) (Fin d) ℝ))) =
      {σ.permMatrix ℝ | σ : Equiv.Perm (Fin d)} :=
  _root_.extremePoints_doublyStochastic

end TNLean
