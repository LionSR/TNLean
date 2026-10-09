/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TerminalSplits
import TNLean.PEPS.AreaLaw.Scan.SplitCounting

/-! Executable stock-axiom assertions for actual band geometry. -/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw.Scan.CollarScan

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_near_middle_subset_later_near'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms state_near_middle_subset_later_near

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_near_middle_subset_later_near'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms oldChargeState_near_middle_subset_later_near

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_near_middle_subset_later_old_near'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms state_near_middle_subset_later_old_near

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.old_near_middle_subset_later_state_near'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms old_near_middle_subset_later_state_near

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_designatedSplitIncidence_unique_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms state_designatedSplitIncidence_unique_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.old_designatedSplitIncidence_unique_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms old_designatedSplitIncidence_unique_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_designatedSplitIncidence_isTerminalSplit_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms state_designatedSplitIncidence_isTerminalSplit_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.old_designatedSplitIncidence_isTerminalSplit_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms old_designatedSplitIncidence_isTerminalSplit_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_card_state_designatedSplitIncidence_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_card_state_designatedSplitIncidence_le_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_card_old_designatedSplitIncidence_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_card_old_designatedSplitIncidence_le_domainGraph

