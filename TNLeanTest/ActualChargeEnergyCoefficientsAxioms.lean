/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyCoefficients

/-! # Stock axioms for actual charge coefficient absorption -/

set_option autoImplicit false
set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeEntropyDefect_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeEntropyDefect_nonneg

/--
info: 'TNLean.PEPS.AreaLaw.Scan.exists_actualCharge_energy_coefficients'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.exists_actualCharge_energy_coefficients
