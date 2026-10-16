/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaPrevectorProperties
import TNLean.PEPS.AreaLaw.Scan.RoughSelectionBudget
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the scanner selection lemmas

The two declarations preserve the supplied prevector and the selected charge point.
-/

run_cmd do
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.augmented_prevector_properties_of_global,
    ``TNLean.PEPS.AreaLaw.Scan.selected_density_of_rough_endpoint]
  let env ← Lean.getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in declarations do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) && allowed.all (axioms.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
