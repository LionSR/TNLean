/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainRelativeGeneratorLocalization

/-! # Kernel dependencies of regional-expectation and domain generator estimates -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'QuantumCircuit.norm_sub_siteExpectation_le_two_mul_norm_sub_of_mem_supportedOperators'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.norm_sub_siteExpectation_le_two_mul_norm_sub_of_mem_supportedOperators

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.norm_relativeGenerator_sub_siteExpectation_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.norm_relativeGenerator_sub_siteExpectation_le
