/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ChargeEntropyCost
import TNLean.PEPS.AreaLaw.Scan.ActualChargeData

/-! # Expected kernel dependencies of actual charge entropy sampling -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TensorPower.ReplicaTransport.moveEta_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.moveEta_nonneg

/-- info: 'TensorPower.ReplicaTransport.moveEta_toP_eq_entropy_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.moveEta_toP_eq_entropy_difference

/-- info: 'TensorPower.ReplicaTransport.moveEta_toF_eq_entropy_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.moveEta_toF_eq_entropy_difference

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.quantumChargeMove_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.quantumChargeMove_eta

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.chargeMoveCost_chargeEntropyCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.chargeMoveCost_chargeEntropyCost

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.good_designatedEntropyCost_le_expected_chargeEta_domainGraph' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms good_designatedEntropyCost_le_expected_chargeEta_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeData_isAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeData_isAdmissible
