/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.RegionalSwapSupport

/-!
# Axiom guards for restricting a sheet swap to the interaction support

These guards import the tensor-product and doubled-interaction identities and
require both to use only the three standard logical axioms.
-/

set_option linter.hashCommand false

/--
info: 'TNLean.Lattice.sheetSwapOp_conj_doubledHamiltonian_eq_inter'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.sheetSwapOp_conj_doubledHamiltonian_eq_inter

/--
info: 'TNLean.Lattice.sheetSwapOp_conj_kronecker_eq_inter'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.sheetSwapOp_conj_kronecker_eq_inter
