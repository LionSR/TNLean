/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceColumnCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for actual source-column coordinates

The fixed source bases, literal column matrix and two coordinate identities
must exist in the production modules and depend only on standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.SourceCircuit.allSourceU,
      ``TNLean.PEPS.PairEffect.SourceCircuit.allSourceV,
      ``TNLean.PEPS.PairEffect.SourceCircuit.allSourceLabels,
      ``TNLean.PEPS.PairEffect.SourceCircuit.allSourceBasis,
      ``TNLean.PEPS.PairEffect.SourceCircuit.actualSourceInputBasis,
      ``TNLean.PEPS.PairEffect.SourceCircuit.partialSourceGlobalMatrix,
      ``TNLean.PEPS.PairEffect.SourceCircuit.actualSourceInputBasis_apply,
      ``TNLean.PEPS.PairEffect.SourceCircuit.partialSourceGlobalMatrix_eq_toMatrix] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
