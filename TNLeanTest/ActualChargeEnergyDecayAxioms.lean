/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyDecay

/-! # Expected kernel dependencies of source-scale actual charge energy -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'TNLean.PEPS.AreaLaw.Scan.exists_actualCharge_energy_threshold'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.exists_actualCharge_energy_threshold
