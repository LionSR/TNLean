/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapReplicaAbsorption
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the fixed-scale replica limit and subsequent coefficient threshold. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.Scan.entropy_le_of_replica_comparisons,
      ``TNLean.PEPS.AreaLaw.Scan.exists_bootstrap_comparison_loss_threshold] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
