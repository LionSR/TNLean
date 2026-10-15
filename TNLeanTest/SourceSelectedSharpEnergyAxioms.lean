/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceSelectedSharpEnergy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of same-point source energy -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.final_eightNuDensity_margins,
    ``TNLean.PEPS.AreaLaw.Scan.exists_final_principalDensity_le_eightNu,
    ``TNLean.PEPS.AreaLaw.Scan.exists_final_selectedDensity_le_eightNu,
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_sourceTarget_selected_actualCharge_sharp_energy]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
