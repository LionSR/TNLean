/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolPatchApproximation

/-! # Kernel dependencies of Theorem 1.1 from Proposition 4.1 -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.Approximation in
/-- info:
'TNLean.PEPS.Approximation.polynomialPEPSApproximation_of_adaptivePatchConstraint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polynomialPEPSApproximation_of_adaptivePatchConstraint
