/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairHalfSideArithmetic
import Lean.Util.CollectAxioms

/-! # Logical dependencies of integral repair half-sides -/

run_cmd do
  let ns := `TNLean.PEPS.AreaLaw.Geometry
  let names := #["exists_natPow_repairHalfSide", "exists_natCast_repairHalfSide"]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let decl := Lean.Name.str ns name
    unless (← Lean.getEnv).contains decl do
      throwError "The intended geometric theorem is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
