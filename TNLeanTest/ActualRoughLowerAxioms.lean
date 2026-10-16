/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoughLowerPrevector
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of the actual rough lower rate -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_actualScan_rough_lower_norm,
    ``TNLean.PEPS.AreaLaw.Scan.roughLowerLabelDefect,
    ``TNLean.PEPS.AreaLaw.Scan.roughLowerLabelDefect_label_bound,
    ``TNLean.PEPS.AreaLaw.Scan.roughLowerRemainder,
    ``TNLean.PEPS.AreaLaw.Scan.tendsto_roughLowerRemainder_of_label_dimension,
    ``TNLean.PEPS.AreaLaw.Scan.exists_roughLowerRemainder_threshold,
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_actualScan_suppliedPrevector_rough_lower]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
