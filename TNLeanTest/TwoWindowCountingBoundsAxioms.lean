/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrequencyCounts
import TNLean.Algebra.TwoWindowRankBounds

/-! # Axiom audits for degree sums and two-window counting bounds -/

/-- info:
'Nat.sum_card_fun_sum_eq_and_two_eq_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Nat.sum_card_fun_sum_eq_and_two_eq_le

/-- info:
'Nat.two_window_rank_factor_le_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Nat.two_window_rank_factor_le_pow

/-- info:
'Nat.two_window_rank_sum_le_factor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Nat.two_window_rank_sum_le_factor
