/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Lattice.PartyCircuit.ProtocolDensityError
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of the retained protocol norm and trace estimate -/

run_cmd do
  let decl := ``TNLean.Lattice.PartyCircuit.protocol_norm_and_trace_deficit_le
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) && allowed.all (axioms.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
