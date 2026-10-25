import TNLean.Circuit.LiebRobinson.GraphPropagation

/-! Axiom checks for finite-support graph propagation and its restricted-norm estimate. -/

/--
info: 'QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance

/--
info: 'QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finset

/--
info: 'QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset
