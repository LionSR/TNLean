/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolOriginalCircuit
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the actual chronological protocol operator. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.DyadicProtocol.originalCircuit,
      ``TNLean.PEPS.Approximation.DyadicProtocol.eval_originalCircuit] do
    unless env.contains decl do
      throwError "Missing imported declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
