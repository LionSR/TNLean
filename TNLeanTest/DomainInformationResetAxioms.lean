/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainLogarithmicSeparation
import TNLean.MPS.AreaLaw.InformationReset

/-! # Kernel dependencies of finite-domain information reset -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'TNLean.Lattice.mutualInformation_cores_le_of_reset_unitary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.mutualInformation_cores_le_of_reset_unitary

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.information_reset'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.information_reset

/-- info:
'TNLean.MPS.AreaLaw.ChainHamiltonian.information_reset'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.ChainHamiltonian.information_reset

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.mutualInformation_le_of_logarithmic_separation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.mutualInformation_le_of_logarithmic_separation
