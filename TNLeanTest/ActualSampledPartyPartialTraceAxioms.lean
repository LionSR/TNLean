/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualSampledPartyPartialTrace
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom check for local output traces of the actual sampled contraction -/

set_option linter.hashCommand false

open TNLean.PEPS.PairEffect.SourceCircuit in
run_cmd do
  let decl := ``partialSourceGlobalMatrix_sampled_partialTrace_eq_sum_partyProduct
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
