/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheoremFromTwoFamilies
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Logical dependencies of the conditional area-law consequence. -/

run_cmd do
  let decl := ``TNLean.PEPS.AreaLaw.uniformAreaLaw_of_twoFamilies
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) && allowed.all (axioms.contains ·) do
    throwError "Unexpected logical dependencies for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
