/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualEnergyTerms

/-! Expected foundational dependencies of the actual energy construction. -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.truncatedEnergyTerm_mem_Icc'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.truncatedEnergyTerm_mem_Icc

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.truncatedEnergyTerm_isSupportedOn'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.truncatedEnergyTerm_isSupportedOn

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualEnergyTerms_spec'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualEnergyTerms_spec

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_actualEnergyTerms'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_actualEnergyTerms

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.replicaEnergy_actualEnergyTerms'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.replicaEnergy_actualEnergyTerms
