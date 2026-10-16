/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularInformationGeometry
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for the geometric lemmas used in angular information decay. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.Approximation.AngularGrid.selected_cell_closure_clearance,
      ``TNLean.PEPS.Approximation.AngularGrid.mem_selectedRegion_iff_touches_owner,
      ``TNLean.PEPS.Approximation.dist_sitePosition_eq_supDist] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
