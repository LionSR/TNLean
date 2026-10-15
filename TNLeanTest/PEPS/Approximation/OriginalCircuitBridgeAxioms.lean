/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OriginalCircuitSequence
import TNLean.PEPS.Approximation.OriginalCircuitGateMaps
import TNLean.PEPS.Approximation.OriginalProducerResources
import TNLean.PEPS.Approximation.SheetStackChange
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the chronological identities and exact original
expansions used in the dyadic protocol-to-network implication. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.OriginalCircuit.sequence,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.eval_sequence_zero,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.eval_sequence_succ,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.isExpansionBounded_sequence,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.nonprivateCount_sequence,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.forall_participants_sequence,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.isMonomialBounded_sequence,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.participationCount_comp,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.participationCount_sequence,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.canonicalGateMaps,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.evalWithGateMaps_canonicalGateMaps,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.isGateApproximation_zero_canonicalGateMaps,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.monomialCount_produce_le_of_isMonomialBounded,
      ``TNLean.PEPS.PairEffect.OriginalCircuit.isExpansionBounded_mono] do
    unless env.contains decl do
      throwError "Missing imported declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
