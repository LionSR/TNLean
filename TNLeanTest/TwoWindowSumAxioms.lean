import TNLean.Algebra.TwoWindowSum

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
