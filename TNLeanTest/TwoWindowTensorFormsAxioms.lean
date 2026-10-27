/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
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
