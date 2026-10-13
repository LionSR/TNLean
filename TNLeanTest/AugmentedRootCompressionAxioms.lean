/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedRootCompression
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the root in the original site coordinates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``TNLean.PEPS.AreaLaw.Scan.bandMetric_submatrix_augmentedReplicaConfigurationEquiv,
    ``TNLean.PEPS.AreaLaw.Scan.rootPath_augmented_compressed_bandProduct]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
