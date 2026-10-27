/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.LeftColumns
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard proof checks for the finite left-column construction. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.leftColumns,
      ``TNLean.MPS.AreaLaw.card_leftColumns_le,
      ``TNLean.MPS.AreaLaw.leftColumns_subset_span,
      ``TNLean.MPS.AreaLaw.rightApply_mem_leftSupportSubmodule_leftColumns] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
