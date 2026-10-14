/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedPartyNetwork
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for finite coordinates of the distributed operator network -/

set_option linter.hashCommand false

open TNLean.PEPS.Approximation.DistributedOperatorContraction

run_cmd do
  let decls := #[``toPartyNetwork, ``operatorCoeff_toPartyNetwork]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
