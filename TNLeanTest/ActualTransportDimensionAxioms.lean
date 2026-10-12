/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TransportDimension

/-! # Expected axiom dependencies of actual transport dimension bounds -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan.CollarScan

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.quantumChargeMove_subsystem'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quantumChargeMove_subsystem

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.quantumFillMove_subsystem'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quantumFillMove_subsystem

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.logDim_quantumFillMove_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logDim_quantumFillMove_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.logDim_quantumChargeMove_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logDim_quantumChargeMove_le_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.fillTransportData_logDim_move_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fillTransportData_logDim_move_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.chargeTransportData_logDim_move_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chargeTransportData_logDim_move_le_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.chargeTransportData_logDim_support_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chargeTransportData_logDim_support_le_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.fillTransportData_logDim_support_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fillTransportData_logDim_support_le_domainGraph
