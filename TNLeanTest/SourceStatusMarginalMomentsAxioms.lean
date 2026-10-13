/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceStatusMarginalMoments

/-! Foundational dependencies of the source-scale physical status inputs. -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.Scan.card_compact_collar_le_quadratic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.card_compact_collar_le_quadratic

/-- info: 'TNLean.PEPS.AreaLaw.Scan.eventually_one_le_source_bandCount'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.eventually_one_le_source_bandCount

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_source_statusMarginal_moment_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_source_statusMarginal_moment_bounds
