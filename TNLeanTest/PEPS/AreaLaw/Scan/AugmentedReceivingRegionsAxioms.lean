/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedReceivingRegions

/-! # Expected logical axioms of the augmented receiving-region identities -/

set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.augmentedPartition_eq_images'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms augmentedPartition_eq_images

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_augmentedPartition_eq_target_near_middle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms state_augmentedPartition_eq_target_near_middle

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_augmentedPartition_eq_target_near_middle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oldChargeState_augmentedPartition_eq_target_near_middle
