/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LiebRobinson.SupportSeparation

/-! # Kernel dependencies of graph reset support separation -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'QuantumCircuit.graphBall_subset_of_finite_distance_margin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.graphBall_subset_of_finite_distance_margin

/-- info:
'QuantumCircuit.reset_graphNeighborhood_disjoint_cores'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.reset_graphNeighborhood_disjoint_cores
