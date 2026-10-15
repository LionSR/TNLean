/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateSampledNetworkApproximation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom check for the physical-density contraction approximation from local gate expansions -/

set_option linter.hashCommand false
open TNLean.PEPS.PairEffect.EffectCircuit

run_cmd do
  let decl := ``exists_sampled_contractedOperator_approximate_error_le
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
