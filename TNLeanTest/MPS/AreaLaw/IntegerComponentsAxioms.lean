/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntegerComponents

/-! Logical-dependency checks for reachability and order-connected integer components. -/

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
