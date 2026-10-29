/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.PeriodicPhysicalHierarchy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for the actual periodic physical hierarchy and its cyclic metric. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let env ← Lean.getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``roundedPeriodicDistance_eq_valMinAbs,
      ``roundedPeriodicDistance_triangle,
      ``periodicPhysicalMetricSpace,
      ``card_periodicPhysical_metricRangeBall_le,
      ``physicalPeriodicProjectionRadius,
      ``physicalPeriodicProjectionRadius_spec,
      ``hierarchyProjectionLength_le_physicalPeriodicProjectionRadius,
      ``physicalPeriodicProjectionRadius_lt,
      ``periodicPhysicalTruncatedTerm,
      ``exists_periodicPhysicalTruncatedTerm_localization,
      ``exists_periodicPhysicalHierarchy] do
    unless env.contains decl do
      throwError "Missing audited declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
