/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleRestriction

/-! # Axiom audit for native two-coboundaries -/

/-- info:
'TNLean.Algebra.isMulCoboundary₂_div_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.isMulCoboundary₂_div_iff

/-- info:
'TNLean.Algebra.isMulCocycle₂_of_isMulCoboundary₂_div' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.isMulCocycle₂_of_isMulCoboundary₂_div

/-- info:
'TNLean.Algebra.isMulCoboundary₂_div_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.isMulCoboundary₂_div_self

/-- info:
'TNLean.Algebra.isMulCoboundary₂_div_symm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.isMulCoboundary₂_div_symm

/-- info:
'TNLean.Algebra.isMulCoboundary₂_div_trans' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.isMulCoboundary₂_div_trans

/-- info:
'TNLean.Algebra.H2π_eq_zero_iff_isMulCoboundary₂' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.H2π_eq_zero_iff_isMulCoboundary₂

/-- info:
'TNLean.Algebra.ScalarCocycle.commPhase_eq_of_isMulCoboundary₂_div' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.ScalarCocycle.commPhase_eq_of_isMulCoboundary₂_div

/-- info:
'TNLean.Algebra.ScalarCocycle.H2π_ne_zero_of_commPhase_ne_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.ScalarCocycle.H2π_ne_zero_of_commPhase_ne_one

/-- info:
'TNLean.Algebra.isMulCoboundary₂_div_comap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.isMulCoboundary₂_div_comap
