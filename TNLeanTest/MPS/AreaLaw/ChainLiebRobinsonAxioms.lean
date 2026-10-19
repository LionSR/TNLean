/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LiebRobinson

/-!
# Axiom checks for the contiguous-chain Lieb–Robinson estimates

The commutator bound and real-radius localization bound use only the three
standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.norm_heisenberg_commutator_le_chainDistance'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.norm_heisenberg_commutator_le_chainDistance

/--
info: 'TNLean.MPS.AreaLaw.norm_heisenberg_sub_siteExpectation_chainNeighborhood_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.norm_heisenberg_sub_siteExpectation_chainNeighborhood_le
