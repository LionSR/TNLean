/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyOutputCoordinates

/-!
# Axiom guard for composition of physical and local basis columns

The composition identity must depend only on the three standard logical axioms.
The guard imports its production module and checks the declaration itself.
-/

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.PairEffect.groupByPartyIso_familyPhysicalListBasis_eq_partyListBasis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.groupByPartyIso_familyPhysicalListBasis_eq_partyListBasis
