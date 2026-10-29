/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TreeBasisCounterexample.HardCoreSectorGap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for positive lifting and the actual hard-core sector energy bound. -/

open TNLean.Lattice.TreeBasisCounterexample

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``quadraticLift, ``modeOperator, ``quadraticLift_outer,
      ``quadraticLift_gram, ``posSemidef_quadraticLift, ``quadraticLift_one,
      ``quadraticLift_gap, ``qubitLowering, ``qubitLowering_number,
      ``lowering, ``numberOperator, ``occupation, ``lowering_number,
      ``numberOperator_eq_diagonal, ``isStarProjection_lowering_number,
      ``norm_lowering_le_one, ``norm_lowering_apply_le, ``IsParticleSector,
      ``re_inner_numberOperator, ``sum_norm_lowering_sq_of_sector,
      ``norm_mode_apply_le, ``norm_mode_apply_sq_le,
      ``norm_hardCoreMode_apply_sq_le, ``hardCore_sector_energy_ge] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
