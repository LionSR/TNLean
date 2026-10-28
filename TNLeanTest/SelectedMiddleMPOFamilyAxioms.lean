/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SelectedMiddleMPOFamily
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of selected middle families -/

run_cmd do
  let env ← Lean.getEnv
  let expectations : Array (Lean.Name × Array Lean.Name) := #[
    (``TNLean.MPS.AreaLaw.exists_common_physical_twoMarkerCoefficient_mpo_family,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.actual_common_physical_mpo_card_le,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.actual_common_physical_mpo_card_low_frequency_le,
      #[``propext, ``Classical.choice, ``Quot.sound])]
  for (decl, expected) in expectations do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let actual ← Lean.collectAxioms decl
    unless actual.size == expected.size && actual.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {actual}"
