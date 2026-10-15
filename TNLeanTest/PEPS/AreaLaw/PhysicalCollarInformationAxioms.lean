/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.PhysicalSafeBox
import TNLean.PEPS.AreaLaw.PhysicalCollarInformation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Named standard-axiom checks for the real-clearance safe-box and collar bounds. -/

run_cmd do
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.exists_regionalEntropy_safe_rect_le_boxError,
    ``TNLean.PEPS.AreaLaw.sublinearCollarBound_real]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
