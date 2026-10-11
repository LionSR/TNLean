/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialWeakRectangleShellEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
Check the uniform initial-exponent rectangle and shell estimates against
the standard axioms.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.exists_regionalEntropy_safe_rect_le_rpow,
      ``TNLean.PEPS.AreaLaw.exists_regionalEntropy_weak_rectangle_shell_le_rpow] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
