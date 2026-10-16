/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceSelectedEnergyPower
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of selected energy decay -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.finalSelectedEnergyCap,
    ``TNLean.PEPS.AreaLaw.Scan.final_selectedEnergy_margins,
    ``TNLean.PEPS.AreaLaw.Scan.finalSelectedEnergyCap_le,
    ``TNLean.PEPS.AreaLaw.Scan.eventually_final_selectedEnergy_le_rpow,
    ``TNLean.PEPS.AreaLaw.Scan.exists_final_selectedEnergy_le_rpow,
    ``TNLean.PEPS.AreaLaw.Scan.selectedEnergy_add_remainder_le,
    ``TNLean.PEPS.AreaLaw.Scan.exists_final_selectedEnergy_add_remainder_le_rpow]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
