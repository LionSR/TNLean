/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLeanTest.ActualRoundParameterIntegral

/-! # Expected kernel dependencies of literal-round parameter regularity

These strict guards are source-only until the separately authorized upstream
integration and elaboration. No guard is weakened or replaced by an unchecked print.
-/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.aestronglyMeasurable_transportScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aestronglyMeasurable_transportScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.intervalIntegrable_transportScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intervalIntegrable_transportScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.integrableOn_Icc_transportScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_Icc_transportScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.aestronglyMeasurable_Icc_transportScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aestronglyMeasurable_Icc_transportScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.aestronglyMeasurable_actualFillScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aestronglyMeasurable_actualFillScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.intervalIntegrable_actualFillScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intervalIntegrable_actualFillScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.integrableOn_Icc_actualFillScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_Icc_actualFillScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.aestronglyMeasurable_Icc_actualFillScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aestronglyMeasurable_Icc_actualFillScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.aestronglyMeasurable_actualChargeScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aestronglyMeasurable_actualChargeScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.intervalIntegrable_actualChargeScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intervalIntegrable_actualChargeScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.integrableOn_Icc_actualChargeScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_Icc_actualChargeScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.aestronglyMeasurable_Icc_actualChargeScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aestronglyMeasurable_Icc_actualChargeScanRound_chargeDefect

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.transport_regularity'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transport_regularity

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.transport_zero_pre'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transport_zero_pre

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.transport_zero_copies'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transport_zero_copies

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.fill_regularity'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fill_regularity

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.charge_regularity'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charge_regularity

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.fill_zero_pre'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fill_zero_pre

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.charge_zero_pre'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charge_zero_pre

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.fill_zero_copies'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fill_zero_copies

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.charge_zero_copies'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charge_zero_copies

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.fill_endpoint_identities'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fill_endpoint_identities

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.charge_endpoint_identities'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charge_endpoint_identities

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.actual_right_endpoints'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_right_endpoints

open TNLeanTest.ActualRoundParameterIntegral in
/-- info:
'TNLeanTest.ActualRoundParameterIntegral.charge_regularity_via_scalar'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charge_regularity_via_scalar
