/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DoubledHamiltonian

/-!
# Axiom checks for the doubled chain Hamiltonian

The interaction family and its exact operator identity use only the three
standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.doubled' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.ChainHamiltonian.doubled

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.doubled_operator' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.ChainHamiltonian.doubled_operator
