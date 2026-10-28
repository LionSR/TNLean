/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SelectedMiddleData
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of selected middle data -/

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.core_and_strict_core_subset_selected_middle,
    ``TNLean.MPS.AreaLaw.card_selected_middle_sdiff_strict_core_le,
    ``TNLean.MPS.AreaLaw.exists_physical_selected_window_fixed_middle_data] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
