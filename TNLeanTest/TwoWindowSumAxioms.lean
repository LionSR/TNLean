/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoWindowSum

/-! Executable stock-axiom assertions for the two-window sum decomposition. -/

/-- info:
'Finset.sum_range_eq_five_parts_of_two_windows' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Finset.sum_range_eq_five_parts_of_two_windows

/-- info:
'Fin.sum_univ_eq_five_parts_of_two_windows' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Fin.sum_univ_eq_five_parts_of_two_windows
