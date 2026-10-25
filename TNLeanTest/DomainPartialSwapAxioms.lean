/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainPartialSwap

/-! # Kernel dependencies of doubled domain Hamiltonians and regional swaps -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.doubled'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.doubled

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.doubled_operator'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.doubled_operator

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.swappedDoubled'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.swappedDoubled

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.swappedDoubled_operator'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.swappedDoubled_operator

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.partialSwap_term_difference_spec'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.partialSwap_term_difference_spec

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.partialSwap_difference_eq_sum_crossing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.partialSwap_difference_eq_sum_crossing
