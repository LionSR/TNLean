/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainLiebRobinson

/-!
# Axiom checks for finite-domain geometry and localization

These declarations use only the three standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.domainGraphIsoHasse'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.domainGraphIsoHasse

/--
info: 'TNLean.MPS.AreaLaw.domainGraph_card_sphere_le_two'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.domainGraph_card_sphere_le_two

/--
info: 'TNLean.MPS.AreaLaw.norm_heisenberg_sub_siteExpectation_domainNeighborhood_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.norm_heisenberg_sub_siteExpectation_domainNeighborhood_le
