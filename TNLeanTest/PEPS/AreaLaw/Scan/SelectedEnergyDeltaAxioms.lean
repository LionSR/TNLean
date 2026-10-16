/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SelectedEnergyDelta
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Permitted axioms for the selected energy and its vanishing remainder -/

run_cmd do
  let decls := #[
    ``TNLean.PEPS.AreaLaw.Scan.selectedEnergy_le_of_density_le_add,
    ``TNLean.PEPS.AreaLaw.Scan.tendsto_selectedEnergy_remainder]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
