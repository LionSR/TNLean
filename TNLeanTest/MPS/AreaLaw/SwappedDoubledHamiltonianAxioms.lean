/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SwappedDoubledHamiltonian

/-!
# Axiom checks for the swapped doubled chain Hamiltonian

The interaction family, its operator identity and the explicit ground-state
transport use only the three standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.swappedDoubled'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.MPS.AreaLaw.ChainHamiltonian.swappedDoubled

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.swappedDoubled_operator'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.MPS.AreaLaw.ChainHamiltonian.swappedDoubled_operator

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.doubled_swappedDoubled_isGappedGroundState'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.MPS.AreaLaw.ChainHamiltonian.doubled_swappedDoubled_isGappedGroundState
