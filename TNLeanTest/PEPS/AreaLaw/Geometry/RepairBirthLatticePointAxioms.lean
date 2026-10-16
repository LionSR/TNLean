/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthLatticePoint
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the lattice points in retained births

Each public theorem must exist and have precisely the three standard logical axioms.
-/

run_cmd do
  let ns := `TNLean.PEPS.AreaLaw.Geometry
  let names := #[`repairStage_birth_oldInclusion, `repairStage_exists_integerPoint_mem_birth,
    `repairStage_exists_integerPoint_mem_birth_of_oldInclusion,
    `repairStage_retained_exists_integerPoint_mem_birth]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    let decl := ns ++ n
    unless (← Lean.getEnv).contains decl do
      throwError "The intended geometric declaration is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
