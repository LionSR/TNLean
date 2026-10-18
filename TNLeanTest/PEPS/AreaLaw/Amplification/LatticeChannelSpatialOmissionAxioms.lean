/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.LatticeChannelSpatialOmission

/-! # Kernel dependencies of the omission estimates of the local-products lemma -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw

/-- info:
'TNLean.PEPS.AreaLaw.exists_integrable_and_integral_channelWordOmissionDefect_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_integrable_and_integral_channelWordOmissionDefect_le

/-- info:
'TNLean.PEPS.AreaLaw.exists_domain_integrable_and_integral_channelWordOmissionDefect_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_domain_integrable_and_integral_channelWordOmissionDefect_le

/-- info:
'TNLean.PEPS.AreaLaw.exists_domainConstraintWord_omission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_domainConstraintWord_omission

/-- info:
'TNLean.PEPS.AreaLaw.exists_latticeConstraintWord_omission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_latticeConstraintWord_omission

/-- info:
'TNLean.PEPS.AreaLaw.graph_integrable_and_integral_channelWordOmissionDefect_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_integrable_and_integral_channelWordOmissionDefect_le

/-- info:
'TNLean.PEPS.AreaLaw.latticeConstraintWord_omission_of_positiveConstraints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms latticeConstraintWord_omission_of_positiveConstraints

/-- info:
'TNLean.PEPS.AreaLaw.latticeConstraintWord_omission_of_locality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms latticeConstraintWord_omission_of_locality
