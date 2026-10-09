/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualEntropySampling

/-! # Expected kernel dependencies of actual old-state entropy sampling -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TensorPower.ReplicaTransport.incidence_sum_eq_splitBandEta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.incidence_sum_eq_splitBandEta

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.designatedSplitIncidenceCost_eq_sum_splitEta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.designatedSplitIncidenceCost_eq_sum_splitEta

/-- info: 'TensorPower.realCoherentIntegral_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.realCoherentIntegral_mono

/-- info: 'TensorPower.ReplicaTransport.TransportData.oldFourierCoherentIntegral_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.TransportData.oldFourierCoherentIntegral_mono

/-- info: 'TensorPower.ReplicaTransport.TransportData.oldFourierCoherentIntegral_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.TransportData.oldFourierCoherentIntegral_one

/-- info: 'TensorPower.ReplicaTransport.TransportData.entropyGain_eq_sum_oldFourierCoherentIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.TransportData.entropyGain_eq_sum_oldFourierCoherentIntegral

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.good_sum_splitEta_le_choiceEntropySymbol_domainGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.good_sum_splitEta_le_choiceEntropySymbol_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeEntropyDefect_le_entropyGain_domainGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeEntropyDefect_le_entropyGain_domainGraph
