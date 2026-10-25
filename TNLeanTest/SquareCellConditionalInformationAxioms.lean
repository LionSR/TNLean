/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareCellConditionalInformation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the square-cell conditional information estimate under the collar bound. -/

open TNLean.PEPS.Approximation in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt,
    ``exists_cell_conditionalMutualInformation_le_square_of_sublinearCollarBound]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
