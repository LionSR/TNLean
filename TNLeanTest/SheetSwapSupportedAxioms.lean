/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapSupported

/-!
# Axiom guard for the supported sheet-swap exchange

This guard imports the production theorem and requires it to use only the three
standard logical axioms.
-/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.EncodedFrame.sheetSwapOp_mul_kronecker_of_mem_supportedOperators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.EncodedFrame.sheetSwapOp_mul_kronecker_of_mem_supportedOperators
