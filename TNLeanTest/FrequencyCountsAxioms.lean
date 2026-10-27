/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrequencyCounts

/-!
# Axioms of the frequency-count theorems

The four guarded theorems use only the standard logical axioms.
-/

/-- info:
'Nat.card_fun_sum_eq_and_two_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Nat.card_fun_sum_eq_and_two_eq

/-- info:
'Nat.card_fun_sum_eq_and_two_eq_of_lt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Nat.card_fun_sum_eq_and_two_eq_of_lt

/-- info:
'Nat.card_fun_sum_eq_and_two_eq_of_total' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Nat.card_fun_sum_eq_and_two_eq_of_total

/-- info:
'Nat.card_fun_sum_eq_and_two_eq_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Nat.card_fun_sum_eq_and_two_eq_le
