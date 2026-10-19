/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.CellConditionalInformation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Conditional information of a physical cell: axiom checks

The imported declarations use only propositional extensionality, classical
choice, and quotient soundness.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TNLean.PEPS.Approximation.coarse_mutualInformation_le_of_sublinearCollarBoundAt,
    ``TNLean.PEPS.Approximation.cell_conditionalMutualInformation_le_of_sublinearCollarBoundAt,
    ``TNLean.PEPS.Approximation.exists_cell_conditionalMutualInformation_le_of_sublinearCollarBound]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
