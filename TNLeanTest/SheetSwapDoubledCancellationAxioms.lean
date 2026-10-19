/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.RegionalSwapSupport

/-!
# Axiom guard for the doubled-interaction cancellation

This guard imports the production theorem and requires it to use only the three
standard logical axioms.
-/

set_option linter.hashCommand false

open TNLean.Lattice in
/--
info: 'TNLean.Lattice.sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators
