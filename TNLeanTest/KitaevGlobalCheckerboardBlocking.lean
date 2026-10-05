/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.KitaevNativeGlobalBlocking

/-! # Positive-period physical regrouping and standard-axiom regressions -/

open TNLean.PEPS

example {width height : ℕ} [NeZero width] [NeZero height] :
    Matrix.IsIsometry (kitaevPhysicalBlockingMatrix (width := width) (height := height)) :=
  kitaevPhysicalBlockingMatrix_isIsometry

-- The smallest positive coarse torus is covered by the bond-indexed convention.
example : Matrix.IsIsometry (kitaevPhysicalBlockingMatrix (width := 1) (height := 1)) :=
  kitaevPhysicalBlockingMatrix_isIsometry

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.kitaevPeriodicFineCoeff_eq_blocked'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.kitaevPeriodicFineCoeff_eq_blocked

/--
info: 'TNLean.PEPS.torusBondNetwork_kitaevPeriodicElementarySite_eq_quantumDoubleNetwork'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.torusBondNetwork_kitaevPeriodicElementarySite_eq_quantumDoubleNetwork

/--
info: 'TNLean.PEPS.kitaevPhysicalBlockingMatrix_isIsometry'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.kitaevPhysicalBlockingMatrix_isIsometry

/--
info: 'TNLean.PEPS.kitaevPhysicalBlockingMatrix_mulVec_checkerboard'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.kitaevPhysicalBlockingMatrix_mulVec_checkerboard
