/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoCutEdgeSupports

/-! Kernel dependencies of the two-cut edge support classification. -/

/-- info:
'TNLean.MPS.AreaLaw.interval_edge_classification_of_lt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.interval_edge_classification_of_lt
