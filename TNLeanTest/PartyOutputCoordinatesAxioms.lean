/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyOutputCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

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

/-! The shared memory-identification helpers may use any subset of the standard
logical axioms. Check each imported public declaration before collecting its
transitive axiom dependencies, so an absent declaration cannot pass silently. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.Layout.memCongr_cons_tmul,
      ``TNLean.PEPS.PairEffect.Layout.selectedHead_heq,
      ``TNLean.PEPS.PairEffect.Layout.complementaryHead_heq,
      ``TNLean.PEPS.PairEffect.Layout.add_heq] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
