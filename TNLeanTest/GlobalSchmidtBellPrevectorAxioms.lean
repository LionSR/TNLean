/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteSetTruncationSchmidtBellPrevector
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check existence and kernel dependencies of the common-label initial vectors. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.exists_global_schmidtBellPrevector,
      ``TNLean.PEPS.AreaLaw.exists_finiteSetTruncation_schmidtBellPrevector_of_gap] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
