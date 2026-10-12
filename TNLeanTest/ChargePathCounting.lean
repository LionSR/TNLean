/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ChargePathCounting
import Mathlib.Tactic.NormNum

/-!
# Regression tests for finite labelled spatial paths

Coincident anchors retain separate labels, arbitrary repeated visits are allowed,
and the empty path is counted exactly once.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw.Scan

-- Two labels at one anchor give four distinct two-step words, even at radius zero.
example :
    (chargeAnchorPaths (⊥ : SimpleGraph (Fin 1)) (fun _ : Fin 2 ↦ 0) 0 0 2).card = 4 := by
  norm_num [chargeAnchorPaths, nearbyChargeLabels, Finset.univ_fin2]

example (labels : List (Fin 2)) :
    labels ∈ chargeAnchorPaths (⊥ : SimpleGraph (Fin 1)) (fun _ : Fin 2 ↦ 0) 0 0 3 ↔
      labels.length = 3 := by
  rw [mem_chargeAnchorPaths_iff]
  simp only [mul_zero, Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff,
    Fin.isValue, List.map_const', and_iff_left_iff_imp]
  intro h
  rw [h]
  decide

example (j : ℕ) :
    (chargeAnchorPaths (⊥ : SimpleGraph (Fin 1)) (fun _ : Fin 2 ↦ 0) 0 0 j).card ≤ 2 ^ j := by
  apply card_chargeAnchorPaths_le
  intro x
  have hx : x = 0 := Fin.eq_zero x
  subst x
  simp [nearbyChargeLabels]

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.Scan.mem_chargeAnchorPaths_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_chargeAnchorPaths_iff

/--
info: 'TNLean.PEPS.AreaLaw.Scan.card_chargeAnchorPaths_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_chargeAnchorPaths_le

/--
info: 'TNLean.PEPS.AreaLaw.Scan.card_nearbyChargeLabels_le_of_vertex_count'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_nearbyChargeLabels_le_of_vertex_count


/--
info: 'TNLean.PEPS.AreaLaw.Scan.card_chargeAnchorPaths_domainGraph_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_chargeAnchorPaths_domainGraph_le


/--
info: 'TNLean.PEPS.AreaLaw.Scan.card_nearbyChargeLabels_domainGraph_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_nearbyChargeLabels_domainGraph_le
