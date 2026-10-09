/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.EdgeCrossingBudget

/-! Guarded kernel dependency reports for the exact crossing budget. -/

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.not_mem_crossingTerms_singleton'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.not_mem_crossingTerms_singleton

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.pair_inter_eq_singleton_of_crossing'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.pair_inter_eq_singleton_of_crossing

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.card_pair_insideConfig_of_crossing'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_pair_insideConfig_of_crossing

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.nearestNeighborSupport'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.nearestNeighborSupport

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.inl_not_mem_crossingTerms'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.inl_not_mem_crossingTerms

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.inr_mem_crossingTerms_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.inr_mem_crossingTerms_iff

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.card_nearestNeighbor_insideConfig'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_nearestNeighbor_insideConfig

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.card_crossingTerms_nearestNeighbor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_crossingTerms_nearestNeighbor

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.nearestNeighbor_crossing_budget'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.nearestNeighbor_crossing_budget
