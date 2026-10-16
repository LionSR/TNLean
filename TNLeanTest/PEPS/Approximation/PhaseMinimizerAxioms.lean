/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.PhaseMinimizer
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Permitted axioms for the minimizing phase

The imported theorems may depend only on the three standard axioms used
throughout the library.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.Approximation.exists_phase_isMinOn,
      ``TNLean.PEPS.Approximation.exists_phase_le_iff_iInf_le,
      ``TNLean.PEPS.Approximation.hasPEPSApproximation_iff_iInf] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
