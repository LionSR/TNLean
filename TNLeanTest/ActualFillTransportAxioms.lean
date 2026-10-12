/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FillSupportCompatibility
import TNLean.PEPS.AreaLaw.Scan.FillTransportEndpoints

/-! Expected foundational dependencies of the actual deterministic fill transport. -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.quantumFillMove_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.quantumFillMove_apply

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFillData_isAdmissible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFillData_isAdmissible

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.fillTransportData_crossBandCommute'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.fillTransportData_crossBandCommute

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.fillTransportData_supportCompatible_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.fillTransportData_supportCompatible_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFillData_rootPath_one_eq_charge_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFillData_rootPath_one_eq_charge_zero

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.charge_rootPath_one_eq_actualFillData_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.charge_rootPath_one_eq_actualFillData_zero
