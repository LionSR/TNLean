/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainInteractionBudget

/-! # Kernel dependencies of finite-domain interaction estimates -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'TNLean.MPS.AreaLaw.DomainSupport.toChainSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainSupport.toChainSupport

/-- info:
'TNLean.MPS.AreaLaw.DomainSupport.toChainSupport_injective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainSupport.toChainSupport_injective

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.toChain_term'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.toChain_term

/-- info:
'TNLean.MPS.AreaLaw.IsDomainSupport.singleton'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.IsDomainSupport.singleton

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.norm_bound_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.norm_bound_nonneg

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.sum_norm_terms_containing_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.sum_norm_terms_containing_le

/-- info:
'TNLean.MPS.AreaLaw.card_domain_crossingTerms_le_mul_card_boundaryEdges'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.card_domain_crossingTerms_le_mul_card_boundaryEdges

/-- info:
'TNLean.MPS.AreaLaw.card_domain_crossingTerms_mul_two_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.card_domain_crossingTerms_mul_two_le
