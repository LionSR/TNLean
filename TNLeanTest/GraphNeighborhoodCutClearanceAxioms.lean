/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.GraphNeighborhoodCutClearance

/-! # Kernel dependencies of graph-neighborhood cut clearance -/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw in
/-- info:
'TNLean.PEPS.AreaLaw.graphNeighborhood_subset_of_cut_clearance'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graphNeighborhood_subset_of_cut_clearance
