/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedReceivingRegions
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the augmented region identities for completed and pre-charge histories. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.Scan.augmentedPartition_eq_images,
      ``TNLean.PEPS.AreaLaw.Scan.CollarScan.state_augmentedPartition_eq_target_near_middle,
      ``TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_augmentedPartition_eq_target_near_middle
    ] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
