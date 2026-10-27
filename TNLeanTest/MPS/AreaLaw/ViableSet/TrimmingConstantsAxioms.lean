/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.TrimmingConstants
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Permitted-axiom checks for the numerical estimates used in trimming. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.trimming_energy_fraction_le_six_mul_sqrt,
    ``TNLean.MPS.AreaLaw.lvv_trimming_constant_bounds,
    ``TNLean.MPS.AreaLaw.lvv_trimming_energy_bounds] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
