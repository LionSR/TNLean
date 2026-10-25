/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Splitting

/-! Kernel dependencies of the right-supported three-region factorization. -/

/-- info:
'TNLean.Lattice.Sheet.exists_threeSplit_eq_reindex_one_kronecker'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.Lattice.Sheet.exists_threeSplit_eq_reindex_one_kronecker
