import TNLean.Algebra.TwoWindowFamily

/-!
# Axiom audit for the grouped bond sum

The sum theorem includes the defining family and the five-part identity
among its dependencies.
-/

/-- info:
'Fin.sum_twoWindowFamily' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Fin.sum_twoWindowFamily

/-- info:
'Fin.twoWindowFamily_map' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Fin.twoWindowFamily_map
