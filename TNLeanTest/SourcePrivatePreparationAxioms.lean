/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PartialSourceWordEvaluation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for actual private-input preparation

The six preparation declarations must exist in the production module and
depend only on the standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.SourceCircuit.sourcePrivatePreparation,
      ``TNLean.PEPS.PairEffect.SourceCircuit.sources_sourcePrivatePreparation,
      ``TNLean.PEPS.PairEffect.SourceCircuit.partialSourceWord,
      ``TNLean.PEPS.PairEffect.SourceCircuit.sources_partialSourceWord,
      ``TNLean.PEPS.PairEffect.SourceCircuit.eval_sourcePrivatePreparation_tmul,
      ``TNLean.PEPS.PairEffect.SourceCircuit.eval_partialSourceWord_tmul] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
