/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainSupportedGaussianIntegral

/-! # Kernel dependencies of supported Gaussian averaging on a finite domain -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'TNLean.MPS.AreaLaw.exists_supported_gaussian_integral_domain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.exists_supported_gaussian_integral_domain

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.operator_isHermitian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.operator_isHermitian
