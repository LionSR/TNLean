/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.SelectedSchmidtEntropyBounds
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the entropy and dimension bounds for the supplied selected spectrum. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decl := ``TNLean.PEPS.AreaLaw.abs_log_card_and_selectedSchmidtEntropy_sub_le
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
