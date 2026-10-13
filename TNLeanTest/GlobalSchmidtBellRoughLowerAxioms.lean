/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.GlobalSchmidtBellRoughLower
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom check for the physical Schmidt--Bell rough lower comparison. -/

run_cmd do
  let decl := ``TNLean.PEPS.AreaLaw.exists_global_schmidtBellPrevector_rough_lower
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
