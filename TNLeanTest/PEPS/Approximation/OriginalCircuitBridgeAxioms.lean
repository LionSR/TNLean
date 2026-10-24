/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.OriginalCircuitSequence
import TNLean.PEPS.Approximation.OriginalCircuitGateMaps
import TNLean.Lattice.PartyCircuit.OriginalProducerResources
import TNLean.PEPS.Approximation.SheetStackChange
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the chronological identities and exact original
expansions used in the dyadic protocol-to-network implication. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.Lattice.PartyCircuit.OriginalCircuit.sequence,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.eval_sequence_zero,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.eval_sequence_succ,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.isExpansionBounded_sequence,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.nonprivateCount_sequence,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.forall_participants_sequence,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.isMonomialBounded_sequence,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.participationCount_comp,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.participationCount_sequence,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.canonicalGateMaps,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.evalWithGateMaps_canonicalGateMaps,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.isGateApproximation_zero_canonicalGateMaps,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.monomialCount_produce_le_of_isMonomialBounded,
      ``TNLean.Lattice.PartyCircuit.OriginalCircuit.isExpansionBounded_mono] do
    unless env.contains decl do
      throwError "Missing imported declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
