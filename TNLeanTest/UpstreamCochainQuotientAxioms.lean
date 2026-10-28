/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology

/-! # Axiom audit for the arbitrary-cochain quotient comparison -/

/-- info:
'TNLean.Algebra.isMulCoboundary₂_div_iff_quotient_mk_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Algebra.isMulCoboundary₂_div_iff_quotient_mk_eq
