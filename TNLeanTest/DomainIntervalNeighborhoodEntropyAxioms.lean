/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainIntervalNeighborhoodEntropy

/-! # Kernel dependencies of intrinsic neighborhood entropy bounds -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'TNLean.MPS.AreaLaw.regionEntropy_domainNeighborhood_biUnion_intervals_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.regionEntropy_domainNeighborhood_biUnion_intervals_le

/-- info:
'TNLean.MPS.AreaLaw.DomainHamiltonian.regionEntropy_neighborhood_biUnion_intervals_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.DomainHamiltonian.regionEntropy_neighborhood_biUnion_intervals_le
