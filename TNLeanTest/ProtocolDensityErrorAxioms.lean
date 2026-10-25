/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.ProtocolDensityError
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom guard for the error and normalization estimates of the protocol

The telescoping bound, the accumulated vector error, and the protocol and compressed density
estimates may depend only on the standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.Lattice.PartyCircuit.norm_trajectory_sub_reference_le,
      ``TNLean.Lattice.PartyCircuit.norm_trajectory_le,
      ``TNLean.Lattice.PartyCircuit.norm_protocol_sub_reference_le,
      ``TNLean.Lattice.PartyCircuit.rectangularTraceNorm_protocol_density_sub_le,
      ``TNLean.Lattice.PartyCircuit.rectangularTraceNorm_compressed_density_sub_le] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
