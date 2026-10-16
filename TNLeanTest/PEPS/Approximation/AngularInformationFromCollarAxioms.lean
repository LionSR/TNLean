/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.AngularInformationFromCollar
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Permitted axioms for the angular information implication

The imported theorem may depend only on the three standard axioms used
throughout the library.
-/

run_cmd do
  let decl := ``TNLean.PEPS.Approximation.angularInformationBound_of_sublinearCollarBound
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
