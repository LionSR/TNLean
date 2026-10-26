/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainIntervalNeighborhood

/-! # Kernel dependencies of intrinsic interval neighborhoods -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'TNLean.MPS.AreaLaw.domainNeighborhood_eq_interval_of_ordConnected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.domainNeighborhood_eq_interval_of_ordConnected

/-- info:
'TNLean.MPS.AreaLaw.domainNeighborhood_interval_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.domainNeighborhood_interval_eq
