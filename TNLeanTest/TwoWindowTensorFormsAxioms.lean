import TNLean.Algebra.TwoWindowTensorForms

/-!
# Axiom audit for the grouped three-region tensor identities
-/

/-- info:
'Matrix.twoWindowFamily_eq_three_region_forms' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.twoWindowFamily_eq_three_region_forms
