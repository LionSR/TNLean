/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadHistoryGeometricTail

/-!
# Finite bad-history bound regressions

Short horizons cannot contain an ancestry longer than the deterministic
minimum. The first admissible horizon keeps the exact binomial cardinality,
including its endpoint, rather than replacing it by a power of the window.
-/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

namespace TNLeanTest.BadHistoryProbability

private abbrev scan : CollarScan (Fin 1) (Fin 1) where
  graph := ⊥
  A := Finset.univ
  depth := fun _ ↦ 0
  anchor := fun _ ↦ 0
  n := 10
  m := 32
  K := 1
  D := 8
  r₀ := 1
  C₁ := 1000

example : scan.badEndpointTail 0 1 = 0 ∧ scan.badEndpointTail 1 1 = 0 ∧
    scan.badEndpointTail 2 1 = 0 := by
  norm_num [CollarScan.badEndpointTail, scan, Finset.sum_filter, Finset.sum_range_succ]

example : scan.badEndpointTail 3 1 = (13 / 160000 : ℝ) ^ 3 := by
  norm_num [CollarScan.badEndpointTail, recentChargeTimes, scan,
    CollarScan.M, chargeSlotCount, Finset.sum_filter, Finset.sum_range_succ]

-- The inclusive backward window of width0 contains its final charge slot.
example : recentChargeTimes 5 0 = {4} ∧ (recentChargeTimes 5 0).card = 1 := by decide

-- A one-pair horizon has only one time, irrespective of a large nominal backward width.
example : (recentChargeTimes 1 100).card.choose 2 = 0 := by decide

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_chargePathWeight_bad_endpoint_domainGraph_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.sum_chargePathWeight_bad_endpoint_domainGraph_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_historyWeight_bad_completed_domainGraph_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.sum_historyWeight_bad_completed_domainGraph_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_historyWeight_bad_through_domainGraph_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.sum_historyWeight_bad_through_domainGraph_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_historyWeight_bad_through_geometric_domainGraph_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.sum_historyWeight_bad_through_geometric_domainGraph_le

end TNLeanTest.BadHistoryProbability
