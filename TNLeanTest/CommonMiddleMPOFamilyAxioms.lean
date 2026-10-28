/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CommonMiddleMPOFamily
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for CommonMiddleMPOFamily -/

run_cmd do
  let env ← Lean.getEnv
  let checks : Array (Lean.Name × Array Lean.Name) := #[
    (``TNLean.MPS.AreaLaw.selected_middle_fixed_interval_bounds,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.actual_common_fixed_middle_mpo_card_low_frequency_le,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.exists_common_fixed_middle_grid_mpo_family,
      #[``propext, ``Classical.choice, ``Quot.sound])
  ]
  for (decl, expected) in checks do
    unless env.contains decl do
      throwError "Missing public declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
