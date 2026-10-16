/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairFinalLatticePartition
import Lean.Util.CollectAxioms

/-! # Logical dependencies of the final lattice partition at an empty generation -/

run_cmd do
  let ns := `TNLean.PEPS.AreaLaw.Geometry.RepairMetricHypotheses
  let declarations := #[
    Lean.Name.str ns "current_disjoint_terminalInteriors_of_isEmpty",
    Lean.Name.str ns "lattice_mem_terminal_or_unique_final_of_isEmpty"]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended geometric theorem is absent: {decl}"
    let expected := #[``propext, ``Classical.choice, ``Quot.sound]
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
