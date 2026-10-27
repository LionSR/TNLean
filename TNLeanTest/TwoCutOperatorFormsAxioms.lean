/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.RegionalOperatorForms
import TNLean.MPS.AreaLaw.TwoCutOperatorForms

/-! Kernel dependencies of the ordinary regional forms and the two-cut family theorem. -/

/-- info:
'TNLean.Lattice.Sheet.exists_threeSplit_eq_kronecker_one_kronecker_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Lattice.Sheet.exists_threeSplit_eq_kronecker_one_kronecker_one

/-- info:
'TNLean.Lattice.Sheet.exists_threeSplit_eq_one_kronecker'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Lattice.Sheet.exists_threeSplit_eq_one_kronecker

/-- info:
'TNLean.MPS.AreaLaw.exists_threeSplit_edge_factors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.exists_threeSplit_edge_factors
