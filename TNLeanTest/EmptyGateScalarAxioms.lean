/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.EmptyGateScalar
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for empty-participant gate scalars

The five scalar declarations must exist in the production modules and depend
only on the standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.PreparedSourceGate.eval_heq_coeffSum_smul_id_of_isEmpty,
      ``TNLean.PEPS.PairEffect.PreparedSourceGate.norm_coeffSum_le_one_of_isEmpty,
      ``TNLean.PEPS.PairEffect.SourceCircuit.emptyGateScalar,
      ``TNLean.PEPS.PairEffect.SourceCircuit.emptyGateScalar_gate_of_isEmpty,
      ``TNLean.PEPS.PairEffect.SourceCircuit.norm_emptyGateScalar_le_one] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
