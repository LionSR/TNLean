/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import TNLean.PEPS.AreaLaw.Geometry.RepairFinalRegionTransport

/-! Logical dependencies of final-region retention and its empty-generation specialization. -/

run_cmd do
  let ns := `TNLean.PEPS.AreaLaw.Geometry
  let names := #["repairFinalRegion_eq_final_oldInclusion",
    "repairFinalRegion_eq_current_oldInclusion_of_isEmpty"]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let decl := Lean.Name.str ns name
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
