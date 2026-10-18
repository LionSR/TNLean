/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.InformationReset

/-!
# Axiom check for information reset on a contiguous chain

The information-reset theorem uses only the three standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.information_reset'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.ChainHamiltonian.information_reset
