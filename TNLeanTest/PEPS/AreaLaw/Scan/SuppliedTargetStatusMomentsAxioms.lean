/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SuppliedTargetStatusMoments
import Lean.Util.CollectAxioms

/-! # Permitted axioms for the supplied-state marginal moment estimates -/

run_cmd do
  let decl :=
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_suppliedTarget_statusMarginal_moment_bounds
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
