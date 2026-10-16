/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.CellConditionalInformationFromGap
import TNLean.PEPS.Approximation.AngularInformationFromGap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Permitted axioms for cell and angular information from the spectral gap

Both imported declarations must exist and may use only the three standard axioms.
-/

run_cmd do
  let decls := #[
    ``TNLean.PEPS.Approximation.exists_cell_conditionalMutualInformation_le_square,
    ``TNLean.PEPS.Approximation.angularInformationBound]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
