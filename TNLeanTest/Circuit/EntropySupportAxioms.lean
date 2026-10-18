/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.EntropySupport

/-!
# Axiom checks for the two operator-support predicates

Both implications use only the three standard axioms of Lean.
-/

/--
info: 'QuantumCircuit.isSupportedOn_of_mem_supportedOperators' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.isSupportedOn_of_mem_supportedOperators

/--
info: 'QuantumCircuit.mem_supportedOperators_of_isSupportedOn' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.mem_supportedOperators_of_isSupportedOn
