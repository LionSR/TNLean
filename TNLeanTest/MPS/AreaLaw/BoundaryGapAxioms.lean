/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BoundaryGap

/-! # Axiom guard for the range-one boundary gap estimate -/

/-- info:
'TNLean.MPS.AreaLaw.ChainHamiltonian.gap_le_four_mul_of_range_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.ChainHamiltonian.gap_le_four_mul_of_range_one
