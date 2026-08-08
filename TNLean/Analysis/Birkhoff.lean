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

**Scope restriction (Wolf Theorem 8.6):** only the doubly-stochastic half is
formalized; the doubly-substochastic half (definition, polytope structure,
extreme partial-permutation-matrix characterization) is missing.
See `docs/paper-gaps/wolf_ch8_birkhoff_doubly_substochastic_gap.tex`.
-/

namespace TNLean

/--
**Birkhoff's theorem** (Wolf Theorem 8.6, Chapter 8, lines 263–266).

The set of `d × d` doubly stochastic matrices over `ℝ` equals the convex
hull of the `d × d` permutation matrices.

**Scope restriction (Wolf Theorem 8.6):** only the doubly-stochastic half is
formalized; the doubly-substochastic half is missing.
See `docs/paper-gaps/wolf_ch8_birkhoff_doubly_substochastic_gap.tex`.
-/
theorem wolf_birkhoff_doublyStochastic_convexHull {d : ℕ} :
    (doublyStochastic ℝ (Fin d) : Set (Matrix (Fin d) (Fin d) ℝ)) =
      convexHull ℝ {σ.permMatrix ℝ | σ : Equiv.Perm (Fin d)} :=
  _root_.doublyStochastic_eq_convexHull_permMatrix

/--
**Birkhoff's theorem** (Wolf Theorem 8.6, Chapter 8, lines 263–266).

The extreme points of the set of `d × d` doubly stochastic matrices over
`ℝ` are exactly the `d × d` permutation matrices.

**Scope restriction (Wolf Theorem 8.6):** only the doubly-stochastic half is
formalized; the doubly-substochastic half is missing.
See `docs/paper-gaps/wolf_ch8_birkhoff_doubly_substochastic_gap.tex`.
-/
theorem wolf_birkhoff_extremePoints_doublyStochastic {d : ℕ} :
    Set.extremePoints ℝ ((doublyStochastic ℝ (Fin d) : Set (Matrix (Fin d) (Fin d) ℝ))) =
      {σ.permMatrix ℝ | σ : Equiv.Perm (Fin d)} :=
  _root_.extremePoints_doublyStochastic

end TNLean
