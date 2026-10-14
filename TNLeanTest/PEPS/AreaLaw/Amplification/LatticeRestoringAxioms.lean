/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.LatticeRestoring

/-! Standard-axiom audit for the restoring operator of the amplification proof. -/

set_option linter.mathlibStandardSet true

/--
info: 'Matrix.partialTraceRight_kronecker_one_mul_mul'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialTraceRight_kronecker_one_mul_mul

/--
info: 'Matrix.partialTraceLeft_kronecker_one_conj'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialTraceLeft_kronecker_one_conj

/--
info: 'Matrix.isStarProjection_kronecker'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isStarProjection_kronecker

/--
info: 'Matrix.norm_projection_mulVec_sub_sq'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_projection_mulVec_sub_sq

/--
info: 'Matrix.PosSemidef.spectralSelection_le_smul'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.spectralSelection_le_smul

/--
info: 'Matrix.IsHermitian.spectralSelection_mul_mul_le_smul'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsHermitian.spectralSelection_mul_mul_le_smul

/--
info: 'TNLean.PEPS.AreaLaw.restoringReducedDensity_restoringVector'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.restoringReducedDensity_restoringVector

/--
info: 'TNLean.PEPS.AreaLaw.partialTraceRight_restoringReducedDensity_restoringVector'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.partialTraceRight_restoringReducedDensity_restoringVector

/--
info: 'TNLean.PEPS.AreaLaw.partialTraceLeft_restoringReducedDensity_restoringVector'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.partialTraceLeft_restoringReducedDensity_restoringVector

/--
info: 'TNLean.PEPS.AreaLaw.norm_restoringVector'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.norm_restoringVector

/--
info: 'TNLean.PEPS.AreaLaw.norm_selectedProjection_restoringVector_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.norm_selectedProjection_restoringVector_sub_le

/--
info: 'TNLean.PEPS.AreaLaw.norm_typicalProjection_restoringVector_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.norm_typicalProjection_restoringVector_sub_le

/--
info: 'TNLean.PEPS.AreaLaw.restoringCutProjection_isStarProjection_commute'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.restoringCutProjection_isStarProjection_commute

/--
info: 'TNLean.PEPS.AreaLaw.norm_restoringCutProjection_restoringVector_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.norm_restoringCutProjection_restoringVector_sub_le

/--
info: 'TNLean.PEPS.AreaLaw.mutualInformation_compl_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.mutualInformation_compl_eq

/--
info: 'TNLean.PEPS.AreaLaw.restoringCutProjection_le_and_typicalProjection_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.restoringCutProjection_le_and_typicalProjection_le

/--
info: 'TNLean.PEPS.AreaLaw.restoringOperator_estimates'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.restoringOperator_estimates

/--
info: 'TNLean.PEPS.AreaLaw.exists_restoringOperator_estimates'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.exists_restoringOperator_estimates
