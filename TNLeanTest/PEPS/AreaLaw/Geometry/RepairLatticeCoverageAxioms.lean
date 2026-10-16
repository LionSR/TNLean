/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairLatticeCoverage
import Lean.Util.CollectAxioms

/-! # Logical dependencies of one-step and actual-stage lattice coverage -/

run_cmd do
  let ns := `TNLean.PEPS.AreaLaw.Geometry
  let declarations := #[
    Lean.Name.str ns "exists_mem_repairNextCurrentRegion_or_terminalInterior",
    Lean.Name.str (Lean.Name.str ns "RepairMetricHypotheses")
      "lattice_mem_current_or_terminal_before"]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended geometric theorem is absent: {decl}"
    let expected := #[``propext, ``Classical.choice, ``Quot.sound]
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
