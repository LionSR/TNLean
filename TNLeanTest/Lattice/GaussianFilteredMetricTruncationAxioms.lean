/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredMetricTruncation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for physical metric Gaussian truncation and its ground-vector bounds. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``exists_metric_truncated_filter_budget,
      ``metric_truncated_filter_properties,
      ``exists_metric_truncated_filter_localization,
      ``exists_metric_truncated_filter_sum_bound] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
