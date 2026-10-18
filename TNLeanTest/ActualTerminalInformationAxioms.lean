/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalInformation

/-! Expected kernel dependencies of the actual terminal information inequality. -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan.CollarScan

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.two_mutualInformation_le_actualTerminal_entropy_average'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_mutualInformation_le_actualTerminal_entropy_average
