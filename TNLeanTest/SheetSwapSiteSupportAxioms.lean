/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.RegionalSwapSupport

/-!
# Axiom guard for the support of the regional sheet swap

This guard imports the production theorem and requires it to use only the three
standard logical axioms.
-/

set_option linter.hashCommand false

/--
info: 'TNLean.Lattice.reindex_sheetSwapOp_mem_supportedOperators'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.reindex_sheetSwapOp_mem_supportedOperators
