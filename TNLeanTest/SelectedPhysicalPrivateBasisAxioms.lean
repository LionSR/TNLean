/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SelectedPhysicalPrivateBasis
import TNLean.PEPS.Approximation.SelectedPhysicalConfigurations
import TNLean.PEPS.Approximation.SelectedPhysicalPartyGrouping
import TNLean.PEPS.Approximation.SelectedPhysicalPrivateGrouping
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for the actual physical/private columns and configurations -/

set_option linter.hashCommand false

run_cmd do
  let decls := #[
    ``TNLean.PEPS.PairEffect.selectedPhysicalPrivateBasis,
    ``TNLean.PEPS.PairEffect.selectedPhysicalPrivateBasis_apply_heq,
    ``TNLean.PEPS.PairEffect.selectedFamilyPhysicalConfigEquiv,
    ``TNLean.PEPS.PairEffect.partyProductMatrix_selectedFamilyPhysicalConfig,
    ``TNLean.PEPS.PairEffect.selectedPartyOrder,
    ``TNLean.PEPS.PairEffect.selectedPartyOrder_nodup,
    ``TNLean.PEPS.PairEffect.mem_selectedPartyOrder,
    ``TNLean.PEPS.PairEffect.selectedFamilyPhysicalPartyBasis_grouped,
    ``TNLean.PEPS.PairEffect.selectedPhysicalPrivateBasis_grouped]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
