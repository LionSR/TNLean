/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoWindowFamilyCardinality
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of the common-family cardinality bound -/

open Lean in
run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let decl := ``TNLean.MPS.AreaLaw.crossing_grid_cardinality_le_square
  let axioms ← Lean.collectAxioms decl
  unless axioms.size == expected.size && axioms.all (expected.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
