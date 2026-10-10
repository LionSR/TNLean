/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapRoundedClearance

/-!
Check the rounded sublinear scale and its scalar and fixed-bootstrap
clearance consequences against the standard axioms.
-/

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.exists_two_mul_floor_rpow_ceil_mul_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.exists_two_mul_floor_rpow_ceil_mul_le

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.mul_collar_add_collar_le_of_two_mul_le'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.mul_collar_add_collar_le_of_two_mul_le

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.exists_bootstrap_collar_clearance'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.exists_bootstrap_collar_clearance
