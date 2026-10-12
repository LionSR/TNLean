/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapDoubledTermNorm

/-!
# Axiom guard for the swapped doubled-interaction norm estimate

This guard imports the production theorem and requires it to use only the three
standard logical axioms.
-/

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.EncodedFrame.norm_sheetSwapOp_conj_doubledHamiltonian_sub_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.EncodedFrame.norm_sheetSwapOp_conj_doubledHamiltonian_sub_le
