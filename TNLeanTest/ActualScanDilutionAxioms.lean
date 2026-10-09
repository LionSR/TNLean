/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.DesignatedDilution

/-! # Executable kernel dependency checks for actual designated-support dilution -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.bandState_assigned_lead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.bandState_assigned_lead

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_assigned_lead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_assigned_lead

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.old_split_anchor_bounds_domainGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.old_split_anchor_bounds_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_split_anchor_bounds_domainGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.state_split_anchor_bounds_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.old_designated_split_dilution_domainGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.old_designated_split_dilution_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_designated_split_dilution_domainGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.state_designated_split_dilution_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.designated_split_mixture_dilution_domainGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.designated_split_mixture_dilution_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.fill_split_mixture_dilution_domainGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.fill_split_mixture_dilution_domainGraph
