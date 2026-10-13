/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyBound

/-! # Expected kernel dependencies of the actual charge energy bound -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan.ScanRound in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.ScanRound.goodOld_le_capacity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms goodOld_le_capacity

open TNLean.PEPS.AreaLaw.Scan.ScanRound in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.ScanRound.energySum_le_of_leaf_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms energySum_le_of_leaf_bounds

open TensorPower.ReplicaTransport in
/-- info:
'TensorPower.ReplicaTransport.splitBandEta_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitBandEta_nonneg

open TensorPower.ReplicaTransport in
/-- info:
'TensorPower.ReplicaTransport.splitBandEta_le_two_mul_logDim'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitBandEta_le_two_mul_logDim

open TensorPower.ReplicaTransport.TransportData in
/-- info:
'TensorPower.ReplicaTransport.TransportData.splitEta_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitEta_nonneg

open TensorPower.ReplicaTransport.TransportData in
/-- info:
'TensorPower.ReplicaTransport.TransportData.splitEta_le_two_mul_of_logDim_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitEta_le_two_mul_of_logDim_le

open TensorPower.ReplicaTransport.TransportData in
/-- info:
'TensorPower.ReplicaTransport.TransportData.measurable_splitEta_sphere'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms measurable_splitEta_sphere

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualCharge_energyError_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualCharge_energyError_le_domainGraph
