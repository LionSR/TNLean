/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationFiniteOrbitDecay
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Permitted-axiom checks for finite-orbit size decay -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.Lattice.translation_half_natDiv_lower_bound,
      ``TNLean.Lattice.exp_neg_half_translation_natDiv_le,
      ``TNLean.Lattice.translation_finiteOrbit_rate_pos,
      ``TNLean.Lattice.translation_exp_floor_decay_le,
      ``TNLean.Lattice.one_le_two_pow_sub_one,
      ``TNLean.Lattice.translation_finiteOrbit_decay_of_near_far] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
