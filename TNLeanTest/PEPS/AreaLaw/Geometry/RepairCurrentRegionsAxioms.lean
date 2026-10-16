/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairCurrentRegions
import Lean.Util.CollectAxioms

/-! # Logical dependencies of openness of the current repair regions -/

run_cmd do
  let ns := `TNLean.PEPS.AreaLaw.Geometry
  let decl := Lean.Name.str ns "isOpen_repairStage_current"
  unless (← Lean.getEnv).contains decl do
    throwError "The intended geometric theorem is absent: {decl}"
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
    throwError "Unexpected logical dependencies for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
