/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.UniformApproximateSampledNetwork
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom check for literal uniform operator networks from original approximate gate expansions -/

set_option linter.hashCommand false
open TNLean.PEPS.PairEffect.GateMapConstruction

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.compressionPrefactor_pos,
      ``TNLean.PEPS.Approximation.compressionExponent_pos,
      ``uniform_approximate_sampled_network_of_le,
      ``exists_uniform_approximate_sampled_network] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
