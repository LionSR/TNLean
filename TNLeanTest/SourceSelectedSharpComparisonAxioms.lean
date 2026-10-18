/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceSelectedSharpComparison

/-! # Kernel dependencies of the common physical selected comparison -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_sourceTarget_selected_actualCharge_sharp_comparison'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_sourceTarget_selected_actualCharge_sharp_comparison

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_sourceTarget_selected_actualCharge_sharp_comparison_of_finiteFamilyTransportBound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  exists_sourceTarget_selected_actualCharge_sharp_comparison_of_finiteFamilyTransportBound
