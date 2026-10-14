/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheorem

/-! # Kernel dependencies of the conditional area-law assembly -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw in
/-- info:
'TNLean.PEPS.AreaLaw.uniformAreaLaw_of_collar_amplification_twoFamilies'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformAreaLaw_of_collar_amplification_twoFamilies
