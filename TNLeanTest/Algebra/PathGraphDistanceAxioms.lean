/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PathGraphDistance

/-!
# Axiom check for distance on a finite open path

The path-distance identity and the sphere bound use only the three standard
axioms of Lean.
-/

/--
info: 'SimpleGraph.pathGraph_edist' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.pathGraph_edist

/--
info: 'SimpleGraph.pathGraph_card_sphere_le_two' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.pathGraph_card_sphere_le_two
