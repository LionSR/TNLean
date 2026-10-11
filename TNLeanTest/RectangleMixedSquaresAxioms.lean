/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RectangleMixedSquares

/-! Kernel dependencies of the mixed-cell count for integer rectangles. -/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.IntRect.card_mixedDyadicIndices_toFinset_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.IntRect.card_mixedDyadicIndices_toFinset_le
