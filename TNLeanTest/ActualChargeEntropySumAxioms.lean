/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEntropySum

/-! # Expected kernel dependencies of the all-round charge bound -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TensorPower.ReplicaTransport.TransportData.entropyGain_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.TransportData.entropyGain_nonneg

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_actualCharge_integral_le_sum_actualRounds_entropyGain_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_actualCharge_integral_le_sum_actualRounds_entropyGain_domainGraph

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualCharges_integral_bound_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualCharges_integral_bound_domainGraph

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualCharges_integral_bound_domainGraph_of_finiteFamilyTransportBound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualCharges_integral_bound_domainGraph_of_finiteFamilyTransportBound
