/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.AngularWholeCellInformationFromCollar
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom check for the conditional whole-cell information estimate

The named theorem is checked for dependence only on the standard logical axioms.
-/

open TNLean.PEPS.Approximation in
run_cmd do
  let decl := ``exists_mutualInformation_selectedRegion_le_square_of_sublinearCollarBound
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
