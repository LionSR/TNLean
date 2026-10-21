/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepLocalCircuits
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! This importing fixture is UNEXECUTED. The entire candidate and its selected
source-only dependencies require elaboration before any declaration or axiom
acceptance is possible. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decl := ``TNLean.MPS.AreaLaw.ChainSweep.local_stage_circuits_of_primitive_information
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
