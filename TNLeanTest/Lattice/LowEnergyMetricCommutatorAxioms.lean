/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyMetricCommutator
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Permitted-axiom checks for growth-free physical-metric commutator decay -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.Lattice.norm_groundCompression_commutator_le_graphSeparation,
      ``TNLean.Lattice.norm_groundCompression_commutator_le_metricSeparation,
      ``TNLean.Lattice.norm_groundCompression_commutator_le_metricBalls,
      ``TNLean.Lattice.norm_groundCompression_metric_truncated_commutator_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
