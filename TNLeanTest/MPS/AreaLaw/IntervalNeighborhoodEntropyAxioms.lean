/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalNeighborhoodEntropy

/-!
# Axiom checks for interval neighborhoods and their entropy

Both declarations use only the three standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.chainNeighborhood_interval_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.chainNeighborhood_interval_eq

/--
info: 'TNLean.MPS.AreaLaw.regionEntropy_chainNeighborhood_biUnion_intervals_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.regionEntropy_chainNeighborhood_biUnion_intervals_le
