/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalBandCommutation

/-! # Executable expected kernel dependencies for physical cross-band commutation -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TensorPower.ReplicaTransport.bandMetric_commute_on_symmetric_of_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.bandMetric_commute_on_symmetric_of_nested

/-- info: 'TensorPower.ReplicaTransport.commute_symBandMetric_of_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.commute_symBandMetric_of_nested

/-- info: 'TNLean.PEPS.AreaLaw.Scan.augmentedPartition_isPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.augmentedPartition_isPartition

/-- info: 'TNLean.PEPS.AreaLaw.Scan.augmentedMove_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.augmentedMove_apply

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.quantumChargeMove_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.quantumChargeMove_apply

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.commute_quantumHistoryPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.commute_quantumHistoryPartition

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.chargeTransportData_crossBandCommute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.chargeTransportData_crossBandCommute
