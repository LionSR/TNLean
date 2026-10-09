/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapRoundedClearance
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
Check the rounded sublinear scale and its scalar and fixed-bootstrap
clearance consequences against the standard axioms.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.Scan.exists_two_mul_floor_rpow_ceil_mul_le,
      ``TNLean.PEPS.AreaLaw.Scan.mul_collar_add_collar_le_of_two_mul_le,
      ``TNLean.PEPS.AreaLaw.Scan.exists_bootstrap_collar_clearance] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
