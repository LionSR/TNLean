/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceEndpointRoughBudget
import TNLean.PEPS.AreaLaw.Scan.RoughSelectionBudget
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of the actual endpoint budget -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.roughEndpointRemainder,
    ``TNLean.PEPS.AreaLaw.Scan.tendsto_roughEndpointRemainder,
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.eventually_actualScan_suppliedPrevector_endpoint_budget,
    ``TNLean.PEPS.AreaLaw.Scan.roughSelectionBudget_le_of_endpoint_budget,
    ``TNLean.PEPS.AreaLaw.Scan.selected_density_le_of_normalized_budget,
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_source_actualScan_suppliedPrevector_endpoint_budget
  ]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
