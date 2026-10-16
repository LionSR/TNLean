/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.UniformApproximateNetworkBounds
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom check for uniform bounds at a fixed local approximation precision -/

set_option linter.hashCommand false
open TNLean.PEPS.PairEffect.EffectCircuit

run_cmd do
  let decl := ``exists_uniform_sampled_approximate_network_bounds
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
