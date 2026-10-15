/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualSharpPrevector
import TNLean.PEPS.AreaLaw.Scan.SourceTargetSharpUpper
import TNLean.PEPS.AreaLaw.Scan.ActualRoughUpper

/-! # Kernel dependencies of the actual sharp upper estimates -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan.CollarScan

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.ActualTerminals.terminalFamily'
does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ActualTerminals.terminalFamily

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.ActualTerminals.terminalPartition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ActualTerminals.terminalPartition

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.ActualTerminals.chargeTerminalIndex'
does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ActualTerminals.chargeTerminalIndex

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.ActualTerminals.actualChargeData_leafPart_terminalPartition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ActualTerminals.actualChargeData_leafPart_terminalPartition

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.ActualTerminals.fillTerminalIndex'
does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ActualTerminals.fillTerminalIndex

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.ActualTerminals.actualFillData_leafPart_terminalPartition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ActualTerminals.actualFillData_leafPart_terminalPartition

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.eventually_actualScan_suppliedPrevector_sharp_upper'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_actualScan_suppliedPrevector_sharp_upper

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_actualScan_schmidtBellPrevector_sharp_upper'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_actualScan_schmidtBellPrevector_sharp_upper

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_truncated_target_actualSharpUpper'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_truncated_target_actualSharpUpper

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.eventually_actualScan_suppliedPrevector_rough_upper'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_actualScan_suppliedPrevector_rough_upper

