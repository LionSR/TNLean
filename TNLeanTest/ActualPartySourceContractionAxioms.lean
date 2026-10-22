/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.AllPartialGate
import TNLean.Lattice.Compression.NoneResidualScalar
import TNLean.Lattice.Compression.NoneSourceWordScalar
import TNLean.Lattice.Compression.ActualPartySourceMatrix
import TNLean.Lattice.Compression.EndpointWordEvaluation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guards for the actual exterior scalar and party coordinates

The nine production declarations must exist and depend only on the standard
logical axioms. The guard includes the endpoint word used in source coordinates.
-/

set_option linter.hashCommand false

open TNLean.Lattice.PartyCircuit.SourceCircuit TNLean.Lattice.PartyCircuit.SourceInventory in
run_cmd do
  let decls := #[
    ``TNLean.PEPS.PairEffect.partySelector_none,
    ``restrict_partialWord_all_gate_localPart_eval_heq_id,
    ``restrict_partialWord_all_localPart_eval_heq_emptyGateScalar,
    ``restrict_partialResidual_all_eval_heq_emptyGateScalar,
    ``restrict_partialSourceWord_all_eval_heq_emptyGateScalar,
    ``actualPartySourceBasisChange,
    ``partialSourcePartyMatrix,
    ``partialSourceGlobalMatrix_eq_partyProduct_mul_basisChange,
    ``eval_endpointWord_slotVector_tmul]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
