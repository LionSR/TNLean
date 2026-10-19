/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapRoundBound
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of the explicit bootstrap round budget -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.Scan.boxBootstrapRounds_le_ceil_log_div,
      ``TNLean.PEPS.AreaLaw.Scan.initialBoxBootstrapRoundBound,
      ``TNLean.PEPS.AreaLaw.Scan.boxBootstrapRounds_initial_le,
      ``TNLean.PEPS.AreaLaw.Scan.pow_initialBoxBootstrapRoundBound_mul_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
