/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusCutBounds

/-! Executable foundational assertions for actual prefix comparisons and cuts. -/

set_option autoImplicit false

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_prefix_sandwich'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.state_prefix_sandwich

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_prefix_sandwich'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_prefix_sandwich

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_prefix_approximation_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.state_prefix_approximation_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_prefix_approximation_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_prefix_approximation_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.card_edgeBoundary_depthPrefix_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.card_edgeBoundary_depthPrefix_le

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.card_edgeBoundary_positiveDepthPrefix_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.card_edgeBoundary_positiveDepthPrefix_le

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.card_edgeBoundary_le_add_four_mul_symmDiff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_edgeBoundary_le_add_four_mul_symmDiff

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_cut_bounds_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.state_cut_bounds_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_cut_bounds_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_cut_bounds_domainGraph
