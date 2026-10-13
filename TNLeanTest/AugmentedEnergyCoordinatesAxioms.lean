/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedEnergyCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the augmented replica energy coordinates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.Scan.augmentedConfigurationEquiv_apply_physical,
      ``TNLean.PEPS.AreaLaw.Scan.augmentedConfigurationEquiv_apply_C,
      ``TNLean.PEPS.AreaLaw.Scan.augmentedConfigurationEquiv_apply_R,
      ``TNLean.PEPS.AreaLaw.Scan.copyMean_augmentOperator_eq_replicaHamiltonian_kronecker] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
