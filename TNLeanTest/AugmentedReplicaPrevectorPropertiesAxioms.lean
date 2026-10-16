/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaPrevectorProperties
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the norm, nonvanishing, symmetry and auxiliary labels of the augmented initial vector. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.norm_augmentedReplicaPrevector_eq_global,
    ``TNLean.PEPS.AreaLaw.Scan.augmentedReplicaPrevector_ne_zero_iff_global,
    ``TNLean.PEPS.AreaLaw.Scan.symProj_mulVec_augmentedReplicaPrevector,
    ``TNLean.PEPS.AreaLaw.Scan.labelProj_auxiliary_mulVec_augmentedReplicaPrevector]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
