/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialRoundedCollarEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the rounded power and uniform physical collar estimates against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.floor_rpow_ceil_mul_rpow_le,
      ``TNLean.PEPS.AreaLaw.exists_regionalEntropy_initial_rounded_collar_le_rpow] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
