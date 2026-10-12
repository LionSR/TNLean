/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapBoundaryExpansion

/-!
# Axiom guard for the crossing-edge expansion

This guard imports the production theorem and requires it to use only the three
standard logical axioms.
-/

set_option linter.hashCommand false

open TNLean.PEPS.Approximation.SquareHamiltonian in
/--
info: 'TNLean.PEPS.Approximation.SquareHamiltonian.sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing
