/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchInsertionTrace
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the complex trace pairing for an insertion in the ordered regularized product. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decl := ``TNLean.PEPS.inner_regularizedPatchInsertion_eq_trace_of_outer_commute
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
