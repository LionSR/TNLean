/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.BirthTargetNeighborhoodInformation

/-! The neighborhood-information boundary estimate uses only the standard
logical axioms. This guard names the imported public theorem exactly. -/

set_option linter.hashCommand false

/-- info:
'TNLean.PEPS.AreaLaw.regionalEntropy_le_boundary_of_neighborhood_information_estimates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.regionalEntropy_le_boundary_of_neighborhood_information_estimates
