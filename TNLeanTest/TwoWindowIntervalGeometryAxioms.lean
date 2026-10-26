import TNLean.MPS.AreaLaw.IntervalSymmDiff

/-!
# Axiom audits for interval displacement and two-window geometry
-/

/-- info:
'TNLean.MPS.AreaLaw.card_interval_symmDiff_le_dist' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.card_interval_symmDiff_le_dist

/-- info:
'TNLean.MPS.AreaLaw.card_two_window_middle_symmDiff_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.card_two_window_middle_symmDiff_le
