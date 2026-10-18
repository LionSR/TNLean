/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductGroundState

/-! Logical-dependency checks for normalized factor ground states and zero-boundary consumers. -/

/--
info: 'TNLean.Lattice.exists_isGappedGroundState_factors_of_kronecker_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.exists_isGappedGroundState_factors_of_kronecker_sum

/--
info: 'TNLean.Lattice.exists_eq_mul_of_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.exists_eq_mul_of_gap

/--
info: 'TNLean.Lattice.vonNeumannEntropy_partialTraceRight_eq_zero_of_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.vonNeumannEntropy_partialTraceRight_eq_zero_of_gap
