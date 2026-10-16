/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoughLowerPrevector
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of the weighted actual rough lower bound -/

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_actualScan_rough_lower_norm_of_weight,
    ``TNLean.PEPS.AreaLaw.Scan.tendsto_roughLowerRemainderAtWeight_of_label_dimension,
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_actualScan_suppliedPrevector_rough_lower_of_weight]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
