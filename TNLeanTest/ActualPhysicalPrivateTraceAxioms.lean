/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualPureSourceReplacement
import TNLean.PEPS.Approximation.DistributedPhysicalPrivateTrace
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for the original physical mixed trace and source expansion -/

set_option linter.hashCommand false

open TNLean.PEPS.PairEffect.SourceCircuit in
run_cmd do
  let decls := #[
    ``TNLean.PEPS.PairEffect.SourceCircuit.sourceReplacedDensity_pure_eq_sum_actualColumns,
    ``TNLean.PEPS.PairEffect.selectedPhysicalPrivateBasis_partialTrace_mixed,
    ``TNLean.PEPS.PairEffect.DistributedConstruction.physicalDensity_eq_grouped_partialTrace]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
