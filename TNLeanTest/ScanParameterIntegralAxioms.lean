/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLeanTest.ActualParameterIntegral
import TNLeanTest.ScanIntegrableSelection

/-! # Stock kernel dependencies of parameter integrability and exact selection -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'TensorPower.ReplicaTransport.TransportData.oldFourierCoherentIntegral_zero_pre'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.TransportData.oldFourierCoherentIntegral_zero_pre

open TensorPower.ReplicaTransport.TransportData in
/-- info:
'TensorPower.ReplicaTransport.TransportData.oldFourierCoherentIntegral_eq_integral_hermPart'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oldFourierCoherentIntegral_eq_integral_hermPart

open TensorPower.ReplicaTransport.TransportData in
/-- info:
'TensorPower.ReplicaTransport.TransportData.aestronglyMeasurable_oldFourierCoherentIntegral'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aestronglyMeasurable_oldFourierCoherentIntegral

/-- info:
'TensorPower.ReplicaTransport.TransportData.abs_oldFourierCoherentIntegral_le'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TensorPower.ReplicaTransport.TransportData.abs_oldFourierCoherentIntegral_le

open TensorPower.ReplicaTransport.TransportData in
/-- info:
'TensorPower.ReplicaTransport.TransportData.intervalIntegrable_oldFourierCoherentIntegral'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intervalIntegrable_oldFourierCoherentIntegral

open TensorPower.ReplicaTransport.TransportData in
/-- info:
'TensorPower.ReplicaTransport.TransportData.intervalIntegrable_sum_oldFourierCoherentIntegral'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intervalIntegrable_sum_oldFourierCoherentIntegral

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.aestronglyMeasurable_actualChargeEntropyDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.aestronglyMeasurable_actualChargeEntropyDefect

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.intervalIntegrable_actualChargeEntropyDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.intervalIntegrable_actualChargeEntropyDefect

/-- info:
'TNLean.PEPS.AreaLaw.Scan.ScanData.intervalIntegrable_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.ScanData.intervalIntegrable_chargeDefect

/-- info:
'TNLean.PEPS.AreaLaw.Scan.sum_integral_le_of_deriv'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.sum_integral_le_of_deriv

/-- info:
'TNLean.PEPS.AreaLaw.Scan.exists_mem_Icc_le_of_sum_integral_le'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.exists_mem_Icc_le_of_sum_integral_le

/-- info:
'TNLean.PEPS.AreaLaw.Scan.exists_selected_density'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.exists_selected_density

/-- info:
'TNLeanTest.ActualParameterIntegral.fill_regularity'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ActualParameterIntegral.fill_regularity

/-- info:
'TNLeanTest.ActualParameterIntegral.charge_zero_pre'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ActualParameterIntegral.charge_zero_pre

/-- info:
'TNLeanTest.ActualParameterIntegral.fill_zero_pre'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ActualParameterIntegral.fill_zero_pre

/-- info:
'TNLeanTest.ActualParameterIntegral.charge_zero_copies'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ActualParameterIntegral.charge_zero_copies

/-- info:
'TNLeanTest.ActualParameterIntegral.fill_zero_copies'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ActualParameterIntegral.fill_zero_copies

/-- info:
'TNLeanTest.ScanIntegrableSelection.discontinuousDefect_no_minimum'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ScanIntegrableSelection.discontinuousDefect_no_minimum

/-- info:
'TNLeanTest.ScanIntegrableSelection.discontinuousDefect_not_continuousOn_Ioo'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ScanIntegrableSelection.discontinuousDefect_not_continuousOn_Ioo

/-- info:
'TNLeanTest.ScanIntegrableSelection.discontinuousDefect_intervalIntegrable'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ScanIntegrableSelection.discontinuousDefect_intervalIntegrable

/-- info:
'TNLeanTest.ScanIntegrableSelection.discontinuousDefect_integral'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ScanIntegrableSelection.discontinuousDefect_integral

/-- info:
'TNLeanTest.ScanIntegrableSelection.discontinuousDefect_exact_selection'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ScanIntegrableSelection.discontinuousDefect_exact_selection

/-- info:
'TNLeanTest.ScanIntegrableSelection.discontinuousDefect_telescope'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLeanTest.ScanIntegrableSelection.discontinuousDefect_telescope
