/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntegerComponents

/-! Logical-dependency checks for integer reachability, components and finite paths. -/

/--
info: 'SimpleGraph.hasse_int_induce_reachable_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.hasse_int_induce_reachable_iff

/--
info: 'SimpleGraph.ConnectedComponent.ordConnected_image_hasse_int_induce' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.ConnectedComponent.ordConnected_image_hasse_int_induce

/--
info: 'SimpleGraph.ConnectedComponent.nonempty_pathGraph_iso_hasse_int_induce_finset'
depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.ConnectedComponent.nonempty_pathGraph_iso_hasse_int_induce_finset
