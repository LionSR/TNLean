/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairRetainedPrimaryErrorSum
import Lean.Util.CollectAxioms

/-! # Logical dependencies of the primary error sum on retained identifiers -/

run_cmd do
  let decl :=
    `TNLean.PEPS.AreaLaw.Geometry.exists_uniform_repairStage_retained_rank_zero_error_sum_bound
  unless (← Lean.getEnv).contains decl do
    throwError "The intended geometric theorem is absent: {decl}"
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
    throwError "Unexpected logical dependencies for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
