/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BoxClearanceComparison
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Named standard-axiom check for the safe-box clearance comparison. -/

run_cmd do
  let decl := ``TNLean.PEPS.AreaLaw.boxEntropy_power_le_of_succ_clearance
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
