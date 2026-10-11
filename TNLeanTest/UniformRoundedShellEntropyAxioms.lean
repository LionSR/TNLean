/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RoundedShellEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the shared rounded powers and uniform conditional shell estimate. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.Scan.exists_bootstrap_collar_clearance,
      ``TNLean.PEPS.AreaLaw.floor_rpow_ceil_mul_rpow_le,
      ``TNLean.PEPS.AreaLaw.Scan.rounded_shell_coefficient_uniform_le,
      ``TNLean.PEPS.AreaLaw.exists_regionalEntropy_rounded_shell_le_uniform_rpow] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
