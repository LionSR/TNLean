/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoundEntropy

/-! Foundational dependencies of actual-round entropy summation. -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualRoundData_rootPath_one_eq_succ_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualRoundData_rootPath_one_eq_succ_zero

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualRoundData_rootPath_one_of_last'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualRoundData_rootPath_one_of_last

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_actualRoundData_logNormSq_sub'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_actualRoundData_logNormSq_sub

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualRoundData_crossBandCommute'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualRoundData_crossBandCommute

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualRounds_entropy_integral_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualRounds_entropy_integral_le_domainGraph
