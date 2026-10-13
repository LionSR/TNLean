/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualScanMeasures

/-! # Expected kernel dependencies, pending upstream acceptance and compilation -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.integral_transportScanRound_old'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_transportScanRound_old

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.integral_transportScanRound_new'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_transportScanRound_new

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportScanRound_mass'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportScanRound_mass

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportScanRound_active'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportScanRound_active

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportScanRound_inactive'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportScanRound_inactive

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportScanRound_choiceGainSum'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportScanRound_choiceGainSum

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportScanRound_splitWeight'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportScanRound_splitWeight

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportScanRound_termEnergy'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportScanRound_termEnergy

open TNLean.PEPS.AreaLaw.Scan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportScanRound_energySum'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportScanRound_energySum

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFillScanRound_mass'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualFillScanRound_mass

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeScanRound_mass'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualChargeScanRound_mass

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFillScanRound_energySum'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualFillScanRound_energySum

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeScanRound_energySum'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualChargeScanRound_energySum

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeScanRound_chargeDefect'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualChargeScanRound_chargeDefect

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFillScanRound_meanEnergy'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualFillScanRound_meanEnergy

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeScanRound_meanEnergy'
    depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualChargeScanRound_meanEnergy
