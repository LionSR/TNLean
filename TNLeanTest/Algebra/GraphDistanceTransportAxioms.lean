/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GraphDistanceTransport

/-!
# Axiom checks for extended graph-distance transport

These declarations use only the three standard axioms of Lean.
-/

/--
info: 'SimpleGraph.Hom.edist_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.Hom.edist_le

/--
info: 'SimpleGraph.Iso.edist_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.Iso.edist_eq

/--
info: 'SimpleGraph.ConnectedComponent.edist_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.ConnectedComponent.edist_eq
