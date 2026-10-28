/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PolynomialFilterParameters
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Permitted-axiom check for the polynomial-filter parameter estimate. -/

run_cmd do
  let decl := ``Real.exists_dg_scalar_parameters
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
