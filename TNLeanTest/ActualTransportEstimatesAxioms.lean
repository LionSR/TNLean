/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTransportEstimates

/-! Expected foundational dependencies; these guards require hosted elaboration. -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFill_transport_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFill_transport_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.actualCharge_transport_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.actualCharge_transport_domainGraph
