/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AmplificationCutClearance
import TNLean.PEPS.AreaLaw.Amplification.GoodRealizationUnitary

/-! # Kernel dependencies of the amplification cut clearance and restoring unitary -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw in
/-- info:
'TNLean.PEPS.AreaLaw.amplificationBound_of_radius_output'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amplificationBound_of_radius_output

open TNLean.PEPS.AreaLaw in
/-- info:
'TNLean.PEPS.AreaLaw.exists_unitary_kronecker_sub_le_of_good_realization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_unitary_kronecker_sub_le_of_good_realization

open TNLean.PEPS.AreaLaw in
/-- info:
'TNLean.PEPS.AreaLaw.norm_truncated_adjoint_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_truncated_adjoint_sub_le
