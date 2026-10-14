/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.ActualInitialRootNorm

/-! # Kernel dependencies of the actual initial normalization bound -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_actualFillData_initial_log_filteredNormSq_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_actualFillData_initial_log_filteredNormSq_bound
