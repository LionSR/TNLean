/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoWindowOperatorForms

/-! # Axiom audit for the independently supplied two-window family -/

/-- info:
'TNLean.MPS.AreaLaw.exists_threeSplit_two_window_factors' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.exists_threeSplit_two_window_factors
