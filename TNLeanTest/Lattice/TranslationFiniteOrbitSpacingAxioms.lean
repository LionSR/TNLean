/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationFiniteOrbitSpacing
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for separated finite translation orbits. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``coordinate_pow_smul,
      ``natAbs_valMinAbs_add_mul_ge_of_near,
      ``edist_pow_mul_ge_of_near] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
