/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology

/-! # Axiom audit for upstream scalar two-cocycles -/

/-- info:
'TNLean.Algebra.isMulCocycle₂_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.isMulCocycle₂_iff

/-- info:
'TNLean.Algebra.ScalarCocycle.isMulCocycle₂_of_projRep' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.ScalarCocycle.isMulCocycle₂_of_projRep

/-- info:
'TNLean.Algebra.H2π_eq_iff_isMulCoboundary₂_div' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.H2π_eq_iff_isMulCoboundary₂_div
