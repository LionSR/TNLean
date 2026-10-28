/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ThreeRegionSupport
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of three-region operator support -/

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.operatorBlock_isSupportedOn_of_threeSplit_left,
    ``TNLean.MPS.AreaLaw.leftBlock_isSupportedOn_of_threeSplit_right,
    ``TNLean.MPS.AreaLaw.eq_of_threeSplit_middle_lift_eq,
    ``TNLean.MPS.AreaLaw.embedOp_subtype_val_submatrix_threeSplit,
    ``TNLean.MPS.AreaLaw.exists_threeSplit_two_window_factors_with_collars,
    ``TNLean.MPS.AreaLaw.exists_weighted_ordinary_middle_eq_central_add_supported] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
