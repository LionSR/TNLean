/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BoundaryCounting

/-!
# Axiom checks for counting interactions at a chain boundary

The boundary-window witness and crossing count use only the three standard
axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.IsChainSupport.exists_boundary_window_of_split'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.IsChainSupport.exists_boundary_window_of_split

/--
info: 'TNLean.MPS.AreaLaw.card_crossingTerms_le_mul_card_boundaryEdges'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.card_crossingTerms_le_mul_card_boundaryEdges
