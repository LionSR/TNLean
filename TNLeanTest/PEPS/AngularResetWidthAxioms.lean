/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularResetWidth

/-! # Axiom reports for the uniform reset-width estimates -/

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.Approximation.exists_reset_scale_polylog_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.exists_reset_scale_polylog_le

/--
info: 'TNLean.PEPS.Approximation.exists_angular_reset_width_bound_of_slope' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.exists_angular_reset_width_bound_of_slope

/--
info: 'TNLean.PEPS.Approximation.exists_angular_reset_width_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.exists_angular_reset_width_bound

/--
info: 'TNLean.PEPS.Approximation.exists_angular_reset_width_lt_of_slope' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.exists_angular_reset_width_lt_of_slope
