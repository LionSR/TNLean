/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationRepair
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationInitial

/-! Standard-axiom audit for both cases of birth-template separation. -/

set_option linter.mathlibStandardSet true
set_option linter.style.longLine false

/-- The explicit angular constant `1/2` at a contact mark: a concrete instance. -/
example : max (1 : ℝ) 0 / 2 ≤ ‖(1 : ℝ) • ((1 : ℝ), (0 : ℝ)) - (0 : ℝ) • ((0 : ℝ), (1 : ℝ))‖ := by
  apply TNLean.PEPS.AreaLaw.Geometry.half_max_le_norm_smul_sub_smul <;> norm_num [Prod.norm_def]

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.half_max_le_norm_sub_of_isQuarterSectorial'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.half_max_le_norm_sub_of_isQuarterSectorial

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_repairSameLabel_dichotomy'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_repairSameLabel_dichotomy

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_repairBirth_separation'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_repairBirth_separation

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.IsIsolatedStar.exists_mem_repairExteriorTrapezoid'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.IsIsolatedStar.exists_mem_repairExteriorTrapezoid

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.isRepairBirthSeparated_of_isUniformRepairInduction'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.isRepairBirthSeparated_of_isUniformRepairInduction

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_isRepairBirthSeparated_of_uniformRepairInductionStatement'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_isRepairBirthSeparated_of_uniformRepairInductionStatement

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_pos_common_contact_dichotomy'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_pos_common_contact_dichotomy

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_beltAtom_dichotomy'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_beltAtom_dichotomy

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_initialBeltRun_birth_separation'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_initialBeltRun_birth_separation

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_isInitialBirthSeparated'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_isInitialBirthSeparated

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_birthSeparation_of_uniformRepairInductionStatement'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_birthSeparation_of_uniformRepairInductionStatement

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_birthSeparation_of_initialIsolatedStars'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_birthSeparation_of_initialIsolatedStars

/--
info: 'TNLean.PEPS.AreaLaw.Geometry.exists_birthSeparation'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_birthSeparation
