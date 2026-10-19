/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.EntropyComparison

/-! Standard-axiom audit for the final entropy comparison of the amplification
proposition. -/

set_option linter.mathlibStandardSet true

/--
info: 'TNLean.Lattice.traceDistance_vecMulVec_le_norm_sub'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.traceDistance_vecMulVec_le_norm_sub

/--
info: 'FiniteProduct.reducedPure_unitary_compl'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.reducedPure_unitary_compl

/--
info: 'FiniteProduct.mutualInformation_le_of_norm_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.mutualInformation_le_of_norm_sub_le

/--
info: 'FiniteProduct.mutualInformation_le_of_unitary_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.mutualInformation_le_of_unitary_sub_le

/--
info: 'FiniteProduct.mutualInformation_le_rpow_of_unitary_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.mutualInformation_le_rpow_of_unitary_sub_le

/--
info: 'FiniteProduct.mutualInformation_le_inv_pow_of_unitary_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.mutualInformation_le_inv_pow_of_unitary_sub_le
