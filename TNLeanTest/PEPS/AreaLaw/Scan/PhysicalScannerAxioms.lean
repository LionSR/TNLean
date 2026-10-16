/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalScanner

/-! # Expected logical axioms of the scanner estimate for the actual scan -/

set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.scanner_estimate_actualScan'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scanner_estimate_actualScan
