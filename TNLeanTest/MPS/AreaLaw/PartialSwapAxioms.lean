/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PartialSwap

/-!
# Axiom checks for the chain partial-swap perturbation

The individual replica estimates and exact crossing decomposition use only
the three standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.partialSwap_term_difference_spec'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.ChainHamiltonian.partialSwap_term_difference_spec

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.partialSwap_difference_eq_sum_crossing'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.ChainHamiltonian.partialSwap_difference_eq_sum_crossing

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.partialSwap_boundary_spec'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.ChainHamiltonian.partialSwap_boundary_spec
