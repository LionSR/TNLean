/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ResetSupportSeparation

/-!
# Axiom check for separation of the reset support from the cores

The geometric separation theorem uses only the three standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.chain_reset_support_separation'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.chain_reset_support_separation
