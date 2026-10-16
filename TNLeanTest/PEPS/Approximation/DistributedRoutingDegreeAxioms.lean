/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedRoutingDegree
import Lean.Util.CollectAxioms

/-! Checks of logical dependencies for the actual distributed-link degree. -/

open TNLean.PEPS.Approximation.DistributedOperatorContraction

run_cmd do
  let env ← Lean.getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``degreeBounded_of_card_incidentDistributedLinks_le,
      ``degreeBounded_of_arity_and_lifetime] do
    unless env.contains decl do
      throwError "Missing imported declaration {decl}"
    let dependencies ← Lean.collectAxioms decl
    unless dependencies.all (allowed.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {dependencies}"
    Lean.logInfo m!"{decl}: {dependencies}"
