/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SelectedDensityPower
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of the source rough power budget -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.eventually_abs_regionalEntropy_sub_le_of_truncation,
    ``TNLean.PEPS.AreaLaw.Scan.roughBudget_le_source_power,
    ``TNLean.PEPS.AreaLaw.Scan.selectedDensity_budget_le_principal,
    ``TNLean.PEPS.AreaLaw.Scan.exists_final_selectedDensity_le]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
