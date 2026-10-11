/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapBoundaryExpansion
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the original crossing-edge expansion against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decl :=
    ``TNLean.PEPS.Approximation.SquareHamiltonian.sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
